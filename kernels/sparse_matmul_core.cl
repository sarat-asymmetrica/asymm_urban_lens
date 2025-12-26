// Sparse Matrix-Vector Multiplication Kernel (Core Operations)
// OpenCL C → SPIR-V → Intel UHD Graphics (24 EU @ 750 MHz)
//
// THE 2GB DAVID EXPERIMENT - LLM Inference on Intel iGPU!
//
// This kernel implements the core sparse matmul for layer-by-layer inference.
// At 80% sparsity: 5× less compute than dense.
//
// Om Gam Ganapataye Namaha 🕉️

// Quaternion struct (16 bytes, matches Rust/Go layout)
typedef struct {
    float w, x, y, z;
} Quaternion;

// ═══════════════════════════════════════════════════════════════════════════════
// CORE KERNEL: Sparse Matrix-Vector Multiplication (CSR Format)
// ═══════════════════════════════════════════════════════════════════════════════
//
// CSR Format:
//   values[nnz]      - Non-zero values
//   col_indices[nnz] - Column index for each value
//   row_ptrs[rows+1] - Start index in values for each row
//
// Complexity: O(nnz) instead of O(rows × cols)

__kernel void sparse_matvec_f32(
    __global const float* values,
    __global const unsigned int* col_indices,
    __global const unsigned int* row_ptrs,
    __global const float* x,
    __global float* y,
    const unsigned int rows
) {
    unsigned int row = get_global_id(0);
    if (row >= rows) return;
    
    unsigned int start = row_ptrs[row];
    unsigned int end = row_ptrs[row + 1];
    
    float sum = 0.0f;
    
    // Process only non-zero elements
    for (unsigned int idx = start; idx < end; idx++) {
        unsigned int col = col_indices[idx];
        float val = values[idx];
        sum += val * x[col];
    }
    
    y[row] = sum;
}

// ═══════════════════════════════════════════════════════════════════════════════
// QUATERNION SPARSE MATMUL (4× batching + sparsity = 20× potential!)
// ═══════════════════════════════════════════════════════════════════════════════

// Quaternion dot product for matmul
float quat_dot4(Quaternion q, float x0, float x1, float x2, float x3, float scale) {
    return (q.w * x0 + q.x * x1 + q.y * x2 + q.z * x3) * scale;
}

__kernel void quaternion_sparse_matvec(
    __global const Quaternion* quaternions,
    __global const float* scales,
    __global const unsigned int* col_indices,
    __global const unsigned int* row_ptrs,
    __global const float* x,
    __global float* y,
    const unsigned int rows,
    const unsigned int cols_blocks
) {
    unsigned int row = get_global_id(0);
    if (row >= rows) return;
    
    unsigned int start = row_ptrs[row];
    unsigned int end = row_ptrs[row + 1];
    
    float sum = 0.0f;
    
    for (unsigned int idx = start; idx < end; idx++) {
        Quaternion q = quaternions[idx];
        float scale = scales[idx];
        unsigned int col_block = col_indices[idx];
        
        unsigned int x_start = col_block * 4;
        float x0 = x[x_start];
        float x1 = x[x_start + 1];
        float x2 = x[x_start + 2];
        float x3 = x[x_start + 3];
        
        sum += quat_dot4(q, x0, x1, x2, x3, scale);
    }
    
    y[row] = sum;
}

// ═══════════════════════════════════════════════════════════════════════════════
// ACTIVATION FUNCTIONS
// ═══════════════════════════════════════════════════════════════════════════════

__kernel void gelu_activation(
    __global float* x,
    const unsigned int n
) {
    unsigned int i = get_global_id(0);
    if (i >= n) return;
    
    float val = x[i];
    float x3 = val * val * val;
    float inner = 0.7978845608f * (val + 0.044715f * x3);
    x[i] = 0.5f * val * (1.0f + tanh(inner));
}

__kernel void silu_activation(
    __global float* x,
    const unsigned int n
) {
    unsigned int i = get_global_id(0);
    if (i >= n) return;
    
    float val = x[i];
    float sigmoid_val = 1.0f / (1.0f + exp(-val));
    x[i] = val * sigmoid_val;
}

// ═══════════════════════════════════════════════════════════════════════════════
// VECTOR OPERATIONS
// ═══════════════════════════════════════════════════════════════════════════════

__kernel void vector_add(
    __global const float* a,
    __global const float* b,
    __global float* y,
    const unsigned int n
) {
    unsigned int i = get_global_id(0);
    if (i >= n) return;
    y[i] = a[i] + b[i];
}

__kernel void vector_scale(
    __global float* x,
    const float scale,
    const unsigned int n
) {
    unsigned int i = get_global_id(0);
    if (i >= n) return;
    x[i] *= scale;
}

// ═══════════════════════════════════════════════════════════════════════════════
// RMSNORM (Used by Phi3)
// ═══════════════════════════════════════════════════════════════════════════════

__kernel void rmsnorm_simple(
    __global float* x,
    __global const float* weight,
    const unsigned int n,
    const float eps
) {
    // Single work-item version for small hidden dims
    // For production: use parallel reduction
    
    float sum_sq = 0.0f;
    for (unsigned int i = 0; i < n; i++) {
        sum_sq += x[i] * x[i];
    }
    
    float rms = sqrt(sum_sq / (float)n + eps);
    float inv_rms = 1.0f / rms;
    
    for (unsigned int i = 0; i < n; i++) {
        x[i] = x[i] * inv_rms * weight[i];
    }
}
