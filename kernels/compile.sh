#!/bin/bash
# SPIR-V Kernel Compilation Script
# OpenCL C → LLVM IR → SPIR-V → Intel N100 GPU
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

echo "🔥 Quaternion OS - SPIR-V Kernel Compiler"
echo "=========================================="

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

# Compile slerp_evolution.cl
echo "📦 Compiling slerp_evolution.cl → slerp_evolution.spv"

# Step 1: OpenCL C → LLVM IR bitcode
clang -cc1 \
    -emit-llvm-bc \
    -triple spir64-unknown-unknown \
    -cl-std=CL3.0 \
    -O3 \
    slerp_evolution.cl \
    -o slerp_evolution.bc

echo "  ✅ LLVM bitcode generated"

# Step 2: LLVM IR → SPIR-V
llvm-spirv slerp_evolution.bc -o slerp_evolution.spv

echo "  ✅ SPIR-V binary generated"

# Verify SPIR-V file
if [ -f slerp_evolution.spv ]; then
    size=$(stat -f%z slerp_evolution.spv 2>/dev/null || stat -c%s slerp_evolution.spv)
    echo "  📊 Size: $size bytes"
    echo ""
    echo "🎉 Compilation successful!"
    echo "   Output: slerp_evolution.spv"
else
    echo "❌ Compilation failed - SPIR-V file not found"
    exit 1
fi

# Clean up intermediate files
rm -f slerp_evolution.bc
echo "🧹 Cleaned up intermediate files"

echo ""
echo "✨ Ready for GPU execution!"
echo "   Use: gpu.LoadKernel(\"kernels/slerp_evolution.spv\", \"slerp_evolution\")"
