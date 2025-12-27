#!/bin/bash
# SPIR-V Kernel Compilation Script - Wave 5 Complete! (Intel oneAPI edition)
set -e

echo "🔥 Quaternion OS - SPIR-V Kernel Compiler (Wave 5)"
echo "=================================================="

# Add Intel oneAPI to PATH
export PATH="/c/Program Files (x86)/Intel/oneAPI/2025.2/bin/compiler:$PATH"

# Check for required tools
if ! command -v clang &> /dev/null; then
    echo "❌ Error: clang not found"
    exit 1
fi

if ! command -v llvm-spirv &> /dev/null; then
    echo "❌ Error: llvm-spirv not found"
    exit 1
fi

echo "✅ Toolchain found (Intel oneAPI LLVM 21.0.0git)"
echo ""

# Function to compile a single kernel
compile_kernel() {
    local kernel_name=$1
    echo "📦 Compiling ${kernel_name}.cl → ${kernel_name}.spv"

    # Step 1: OpenCL C → LLVM IR bitcode
    clang -cc1 \
        -x cl \
        -emit-llvm-bc \
        -triple spir64-unknown-unknown \
        -cl-std=CL3.0 \
        -O3 \
        -finclude-default-header \
        ${kernel_name}.cl \
        -o ${kernel_name}.bc

    echo "  ✅ LLVM bitcode generated"

    # Step 2: LLVM IR → SPIR-V
    llvm-spirv ${kernel_name}.bc -o ${kernel_name}.spv

    echo "  ✅ SPIR-V binary generated"

    # Verify SPIR-V file
    if [ -f ${kernel_name}.spv ]; then
        size=$(stat -c%s ${kernel_name}.spv 2>/dev/null || stat -f%z ${kernel_name}.spv 2>/dev/null || wc -c < ${kernel_name}.spv)
        echo "  📊 Size: $size bytes"
    else
        echo "  ❌ Compilation failed - SPIR-V file not found"
        exit 1
    fi

    # Clean up intermediate files
    rm -f ${kernel_name}.bc
    echo ""
}

# Compile all kernels
compile_kernel "slerp_evolution"
compile_kernel "dual_fovea"
compile_kernel "tetrachromatic"
compile_kernel "consciousness"

echo "🧹 Cleaned up all intermediate files"
echo ""
echo "🎉 All kernels compiled successfully!"
echo "   Output:"
echo "     - slerp_evolution.spv (Wave 1: Core SLERP)"
echo "     - dual_fovea.spv (Wave 2: Adaptive processing)"
echo "     - tetrachromatic.spv (Wave 3: Image evolution)"
echo "     - consciousness.spv (Wave 4: Golden ratio metrics)"
echo ""
echo "✨ Ready for GPU execution on Intel N100!"
echo "   Target: 1.5 BILLION quaternion ops/sec (50-100× CPU speedup!)"
