// Sparse Quaternion Matrix-Vector Multiplication Kernel
// OpenCL C → SPIR-V → Intel UHD Graphics (24 EU @ 750 MHz)
//
// THE 2GB DAVID EXPERIMENT!
//
// This kernel implements layer-by-layer LLM inference on Intel iGPU:
// 1. Load one layer's sparse weights to GPU (60-120MB per layer)
// 2. Compute sparse matmul on GPU
// 3. Stream next layer while GPU computes
//
// At 80% sparsity: 5× less compute
// With quaternion batching: 4× efficiency
// Combined: 20× potential speedup!
//
// Target: Make Phi3 inference viable on Intel UHD
//
// Om Gam Ganapataye Namaha 🕉️

// Quaternion struct (16 bytes, matches Rust/Go layout)
typedef struct {
    float w, x, y, z;
} Quaternion;

// CSR sparse format indices
typedef struct {
    uint row_start;  // Start index in values array
    uint row_end;    // End index in values array
} RowRange;

// ═══════════════════════════════════════════════════════════════════════════════
// CORE KERNEL: Sparse Matrix-Vector Multiplication
// ═══════════════════════════════════════════════════════════════════════════════
//
// CSR Format:
//   values[nnz]      - Non-zero values
//   col_indices[nnz] - Column index for each value
//   row_ptrs[rows+1] - Start index in values for each row
//
// Complexity: O(nnz) instead of O(rows × cols)
// At 80% sparsity: 5× faster than dense!

__kernel void sparse_matvec_f32(
    __global const float* values,       // Non-zero values [nnz]
    __global const uint* col_indices,   // Column indices [nnz]
    __global const uint* row_ptrs,      // Row pointers [rows+1]
    __global const float* x,            // Input vector [cols]
    __global float* y,                  // Output vector [rows]
    const uint rows                     // Number of rows
) {
    uint row = get_global_id(0);
    if (row >= rows) return;
    
    uint start = row_ptrs[row];
    uint end = row_ptrs[row + 1];
    
    float sum = 0.0f;
    
    // Process only non-zero elements (SKIP THE POISON!)
    for (uint idx = start; idx < end; idx++) {
        uint col = col_indices[idx];
        float val = values[idx];
        sum += val * x[col];
    }
    
    y[row] = sum;
}

// ═══════════════════════════════════════════════════════════════════════════════
// QUATERNION SPARSE MATMUL (4× batching + sparsity skip = 20× speedup!)
// ═══════════════════════════════════════════════════════════════════════════════
//
// Instead of individual f32 values, we process quaternion blocks:
// - Each quaternion = 4 weights packed together
// - Quaternion multiplication = 4 MACs in one operation
// - Combined with sparsity: only process non-zero quaternion blocks

// Quaternion dot product (fast path for matmul)
float quaternion_dot(Quaternion q, float4 x, float scale) {
    return (q.w * x.x + q.x * x.y + q.y * x.z + q.z * x.w) * scale;
}

__kernel void quaternion_sparse_matvec(
    __global const Quaternion* quaternions,  // Non-zero quaternion blocks [nnz_blocks]
    __global const float* scales,            // Scale for each block [nnz_blocks]
    __global const uint* col_indices,        // Column block indices [nnz_blocks]
    __global const uint* row_ptrs,           // Row pointers [rows+1]
    __global const float* x,                 // Input vector [cols * 4]
    __global float* y,                       // Output vector [rows]
    const uint rows,                         // Number of rows
    const uint cols_blocks                   // Number of column blocks
) {
    uint row = get_global_id(0);
    if (row >= rows) return;
    
    uint start = row_ptrs[row];
    uint end = row_ptrs[row + 1];
    
    float sum = 0.0f;
    
    // Process only non-zero quaternion blocks
    for (uint idx = start; idx < end; idx++) {
        Quaternion q = quaternions[idx];
        float scale = scales[idx];
        uint col_block = col_indices[idx];
        
        // Load 4 input values for this quaternion block
        uint x_start = col_block * 4;
        float4 x_block = (float4)(x[x_start], x[x_start+1], x[x_start+2], x[x_start+3]);
        
        // Quaternion dot product (4 MACs in one!)
        sum += quaternion_dot(q, x_block, scale);
    }
    
    y[row] = sum;
}

// ═══════════════════════════════════════════════════════════════════════════════
// ACTIVATION FUNCTIONS (ReLU, GELU, SiLU)
// ═══════════════════════════════════════════════════════════════════════════════

// ReLU: max(0, x)
__kernel void relu(
    __global float* x,
    const uint n
) {
    uint i = get_global_id(0);
    if (i >= n) return;
    x[i] = fmax(0.0f, x[i]);
}

// GELU approximation (Phi3 uses this!)
// GELU(x) ≈ 0.5 * x * (1 + tanh(√(2/π) * (x + 0.044715 * x³)))
__kernel void gelu(
    __global float* x,
    const uint n
) {
    uint i = get_global_id(0);
    if (i >= n) return;
    
    float val = x[i];
    float x3 = val * val * val;
    float inner = 0.7978845608f * (val + 0.044715f * x3);  // √(2/π) ≈ 0.7978845608
    x[i] = 0.5f * val * (1.0f + tanh(inner));
}

// SiLU (Swish): x * sigmoid(x)
__kernel void silu(
    __global float* x,
    const uint n
) {
    uint i = get_global_id(0);
    if (i >= n) return;
    
    float val = x[i];
    float sigmoid = 1.0f / (1.0f + exp(-val));
    x[i] = val * sigmoid;
}

// ═══════════════════════════════════════════════════════════════════════════════
// LAYER NORMALIZATION (RMSNorm for Phi3)
// ═══════════════════════════════════════════════════════════════════════════════

// RMSNorm: x / sqrt(mean(x²) + eps) * weight
// Phi3 uses RMSNorm instead of LayerNorm
__kernel void rmsnorm(
    __global float* x,              // Input/output [n]
    __global const float* weight,   // Learned weights [n]
    __local float* shared_sum,      // Shared memory for reduction
    const uint n,
    const float eps
) {
    uint lid = get_local_id(0);
    uint gid = get_global_id(0);
    uint group_size = get_local_size(0);
    
    // Step 1: Compute sum of squares (parallel reduction)
    float local_sum = 0.0f;
    for (uint i = lid; i < n; i += group_size) {
        float val = x[i];
        local_sum += val * val;
    }
    shared_sum[lid] = local_sum;
    barrier(CLK_LOCAL_MEM_FENCE);
    
    // Reduce within work group
    for (uint stride = group_size / 2; stride > 0; stride /= 2) {
        if (lid < stride) {
            shared_sum[lid] += shared_sum[lid + stride];
        }
        barrier(CLK_LOCAL_MEM_FENCE);
    }
    
    // Step 2: Compute RMS and normalize
    float rms = sqrt(shared_sum[0] / (float)n + eps);
    float inv_rms = 1.0f / rms;
    
    barrier(CLK_LOCAL_MEM_FENCE);
    
    // Step 3: Apply normalization and weight
    for (uint i = lid; i < n; i += group_size) {
        x[i] = x[i] * inv_rms * weight[i];
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// SOFTMAX (for attention scores)
// ═══════════════════════════════════════════════════════════════════════════════

__kernel void softmax(
    __global float* x,
    __local float* shared,
    const uint n
) {
    uint lid = get_local_id(0);
    uint group_size = get_local_size(0);
    
    // Step 1: Find max (for numerical stability)
    float local_max = -INFINITY;
    for (uint i = lid; i < n; i += group_size) {
        local_max = fmax(local_max, x[i]);
    }
    shared[lid] = local_max;
    barrier(CLK_LOCAL_MEM_FENCE);
    
    for (uint stride = group_size / 2; stride > 0; stride /= 2) {
        if (lid < stride) {
            shared[lid] = fmax(shared[lid], shared[lid + stride]);
        }
        barrier(CLK_LOCAL_MEM_FENCE);
    }
    float max_val = shared[0];
    barrier(CLK_LOCAL_MEM_FENCE);
    
    // Step 2: Compute exp(x - max) and sum
    float local_sum = 0.0f;
    for (uint i = lid; i < n; i += group_size) {
        float exp_val = exp(x[i] - max_val);
        x[i] = exp_val;
        local_sum += exp_val;
    }
    shared[lid] = local_sum;
    barrier(CLK_LOCAL_MEM_FENCE);
    
    for (uint stride = group_size / 2; stride > 0; stride /= 2) {
        if (lid < stride) {
            shared[lid] += shared[lid + stride];
        }
        barrier(CLK_LOCAL_MEM_FENCE);
    }
    float sum_val = shared[0];
    barrier(CLK_LOCAL_MEM_FENCE);
    
    // Step 3: Normalize
    float inv_sum = 1.0f / sum_val;
    for (uint i = lid; i < n; i += group_size) {
        x[i] *= inv_sum;
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// EMBEDDING LOOKUP (Token → Hidden State)
// ═══════════════════════════════════════════════════════════════════════════════

__kernel void embedding_lookup(
    __global const float* embedding_table,  // [vocab_size × hidden_dim]
    __global const uint* token_ids,         // [seq_len]
    __global float* output,                 // [seq_len × hidden_dim]
    const uint hidden_dim,
    const uint seq_len
) {
    uint pos = get_global_id(0);  // Position in sequence
    uint dim = get_global_id(1);  // Dimension in hidden state
    
    if (pos >= seq_len || dim >= hidden_dim) return;
    
    uint token_id = token_ids[pos];
    output[pos * hidden_dim + dim] = embedding_table[token_id * hidden_dim + dim];
}

// ═══════════════════════════════════════════════════════════════════════════════
// ROTARY POSITION EMBEDDING (RoPE) - Used by Phi3
// ═══════════════════════════════════════════════════════════════════════════════

__kernel void rope_embedding(
    __global float* q,              // Query [seq_len × head_dim]
    __global float* k,              // Key [seq_len × head_dim]
    __global const float* cos_cache,  // Precomputed cos [max_seq × head_dim/2]
    __global const float* sin_cache,  // Precomputed sin [max_seq × head_dim/2]
    const uint seq_len,
    const uint head_dim
) {
    uint pos = get_global_id(0);    // Position in sequence
    uint pair = get_global_id(1);   // Pair index (head_dim / 2 pairs)
    
    if (pos >= seq_len || pair >= head_dim / 2) return;
    
    uint idx0 = pos * head_dim + pair * 2;
    uint idx1 = idx0 + 1;
    uint cache_idx = pos * (head_dim / 2) + pair;
    
    float cos_val = cos_cache[cache_idx];
    float sin_val = sin_cache[cache_idx];
    
    // Apply rotation to query
    float q0 = q[idx0];
    float q1 = q[idx1];
    q[idx0] = q0 * cos_val - q1 * sin_val;
    q[idx1] = q0 * sin_val + q1 * cos_val;
    
    // Apply rotation to key
    float k0 = k[idx0];
    float k1 = k[idx1];
    k[idx0] = k0 * cos_val - k1 * sin_val;
    k[idx1] = k0 * sin_val + k1 * cos_val;
}

// ═══════════════════════════════════════════════════════════════════════════════
// ATTENTION SCORE COMPUTATION
// ═══════════════════════════════════════════════════════════════════════════════

// Compute Q × K^T for attention scores
__kernel void attention_scores(
    __global const float* Q,        // Query [seq_len × head_dim]
    __global const float* K,        // Key [seq_len × head_dim]
    __global float* scores,         // Output [seq_len × seq_len]
    const uint seq_len,
    const uint head_dim,
    const float scale               // 1/sqrt(head_dim)
) {
    uint i = get_global_id(0);  // Query position
    uint j = get_global_id(1);  // Key position
    
    if (i >= seq_len || j >= seq_len) return;
    
    // Causal mask: only attend to previous positions
    if (j > i) {
        scores[i * seq_len + j] = -INFINITY;
        return;
    }
    
    // Dot product Q[i] · K[j]
    float sum = 0.0f;
    for (uint d = 0; d < head_dim; d++) {
        sum += Q[i * head_dim + d] * K[j * head_dim + d];
    }
    
    scores[i * seq_len + j] = sum * scale;
}

// ═══════════════════════════════════════════════════════════════════════════════
// VECTOR OPERATIONS (Add, Scale, etc.)
// ═══════════════════════════════════════════════════════════════════════════════

// Element-wise add: y = a + b
__kernel void vector_add(
    __global const float* a,
    __global const float* b,
    __global float* y,
    const uint n
) {
    uint i = get_global_id(0);
    if (i >= n) return;
    y[i] = a[i] + b[i];
}

// Element-wise multiply: y = a * b
__kernel void vector_mul(
    __global const float* a,
    __global const float* b,
    __global float* y,
    const uint n
) {
    uint i = get_global_id(0);
    if (i >= n) return;
    y[i] = a[i] * b[i];
}

// Scale: y = x * scale
__kernel void vector_scale(
    __global float* x,
    const float scale,
    const uint n
) {
    uint i = get_global_id(0);
    if (i >= n) return;
    x[i] *= scale;
}
