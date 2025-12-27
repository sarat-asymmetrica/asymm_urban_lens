#!/bin/bash
# SPIR-V Kernel Compilation Script - Phase 1 Optimized
# OpenCL C → LLVM IR → SPIR-V → Intel N100 GPU
#
# Compiles PHASE 1 OPTIMIZED kernel with FMA + half_rsqrt
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

echo "🚀 Phase 1 Optimized Kernel - SPIR-V Compiler"
echo "=============================================="

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

# Compile slerp_evolution_optimized.cl
echo "📦 Compiling slerp_evolution_optimized.cl → slerp_evolution_optimized.spv"

# Step 1: OpenCL C → LLVM IR bitcode
# Phase 1 optimizations enabled:
#   -O3: Full LLVM optimization
#   -ffast-math: Enable FMA fusion (critical for 1.2× speedup!)
#   -cl-mad-enable: Allow multiply-add fusion
#   -cl-no-signed-zeros: Relaxed floating point for speed
#   -cl-unsafe-math-optimizations: Aggressive FP optimization
clang -cc1 \
    -emit-llvm-bc \
    -triple spir64-unknown-unknown \
    -cl-std=CL3.0 \
    -O3 \
    -ffast-math \
    -cl-mad-enable \
    -cl-no-signed-zeros \
    -cl-unsafe-math-optimizations \
    slerp_evolution_optimized.cl \
    -o slerp_evolution_optimized.bc

echo "  ✅ LLVM bitcode generated (with FMA + fast math)"

# Step 2: LLVM IR → SPIR-V
llvm-spirv slerp_evolution_optimized.bc -o slerp_evolution_optimized.spv

echo "  ✅ SPIR-V binary generated"

# Verify SPIR-V file
if [ -f slerp_evolution_optimized.spv ]; then
    size=$(stat -f%z slerp_evolution_optimized.spv 2>/dev/null || stat -c%s slerp_evolution_optimized.spv)
    echo "  📊 Size: $size bytes"
    echo ""
    echo "🎉 Phase 1 Optimized Kernel Compiled!"
    echo "   Output: slerp_evolution_optimized.spv"
else
    echo "❌ Compilation failed - SPIR-V file not found"
    exit 1
fi

# Clean up intermediate files
rm -f slerp_evolution_optimized.bc
echo "🧹 Cleaned up intermediate files"

echo ""
echo "✨ Ready for Phase 1 Benchmarking!"
echo "   Use: gpu.LoadKernel(\"kernels/slerp_evolution_optimized.spv\", \"slerp_evolution\")"
echo ""
echo "🎯 Expected Performance:"
echo "   Kernel-level: 1.5-2× faster (FMA + half_rsqrt)"
echo "   System-level: 3-5× faster (+ persistent buffers + async)"
