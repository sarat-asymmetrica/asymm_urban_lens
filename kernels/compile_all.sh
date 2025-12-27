#!/bin/bash
# SPIR-V Kernel Compilation Script - Wave 5 Complete!
# OpenCL C → LLVM IR → SPIR-V → Intel N100 GPU
#
# Compiles ALL kernels (Wave 1-4):
#   - slerp_evolution.cl (Wave 1: Core quaternion SLERP)
#   - dual_fovea.cl (Wave 2: Eagle dual-fovea adaptive)
#   - tetrachromatic.cl (Wave 3: RGBUV image processing)
#   - consciousness.cl (Wave 4: Golden ratio + consciousness metrics)
#
# Requirements:
#   - clang (LLVM/Clang toolchain)
#   - llvm-spirv (SPIR-V translator)
#
# Install on Ubuntu/Debian:
#   sudo apt install clang llvm-spirv
#
# Install on Windows (MSYS2):
#   pacman -S mingw-w64-x86_64-clang mingw-w64-x86_64-llvm

set -e  # Exit on error

echo "🔥 Quaternion OS - SPIR-V Kernel Compiler (Wave 5)"
echo "=================================================="

# Check for required tools
if ! command -v clang &> /dev/null; then
    echo "❌ Error: clang not found"
    echo "Install: sudo apt install clang (Linux) or pacman -S mingw-w64-x86_64-clang (MSYS2)"
    exit 1
fi

if ! command -v llvm-spirv &> /dev/null; then
    echo "❌ Error: llvm-spirv not found"
    echo "Install: sudo apt install llvm-spirv (Linux) or pacman -S mingw-w64-x86_64-llvm (MSYS2)"
    exit 1
fi

echo "✅ Toolchain found"
echo ""

# Function to compile a single kernel
compile_kernel() {
    local kernel_name=$1
    echo "📦 Compiling ${kernel_name}.cl → ${kernel_name}.spv"

    # Step 1: OpenCL C → LLVM IR bitcode
    clang -cc1 \
        -emit-llvm-bc \
        -triple spir64-unknown-unknown \
        -cl-std=CL3.0 \
        -O3 \
        ${kernel_name}.cl \
        -o ${kernel_name}.bc

    echo "  ✅ LLVM bitcode generated"

    # Step 2: LLVM IR → SPIR-V
    llvm-spirv ${kernel_name}.bc -o ${kernel_name}.spv

    echo "  ✅ SPIR-V binary generated"

    # Verify SPIR-V file
    if [ -f ${kernel_name}.spv ]; then
        size=$(stat -f%z ${kernel_name}.spv 2>/dev/null || stat -c%s ${kernel_name}.spv)
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
