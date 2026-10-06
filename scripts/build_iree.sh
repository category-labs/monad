#!/bin/bash
#
# Builds the IREE compiler from third_party/iree, outside the monad build:
# libIREECompiler.so, its embedded linker (iree-lld), and iree-compile, the
# command-line compiler for building kernels ahead of time. LLVM/MLIR never
# enter the monad build and only need rebuilding when the submodule is bumped.
# The IREE runtime is built as part of the monad build.
#
# Environment:
#   IREE_BUILD_DIR   build directory (default: <repo>/build-iree)
#   IREE_BUILD_TYPE  CMake build type (default: Release)
#   CC, CXX          compilers, as for any CMake project
#
# Extra arguments are passed to the CMake configure step, e.g.
#   scripts/build_iree.sh -DIREE_ENABLE_LLD=ON

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$(realpath -m "${IREE_BUILD_DIR:-${repo_root}/build-iree}")"

cmake_args=(
  -S "${repo_root}/third_party/iree"
  -B "${build_dir}"
  -G Ninja
  -DCMAKE_BUILD_TYPE:STRING="${IREE_BUILD_TYPE:-Release}"
  -DIREE_BUILD_COMPILER=ON
  -DIREE_BUILD_TESTS=OFF
  -DIREE_BUILD_BENCHMARKS=OFF
  -DIREE_BUILD_SAMPLES=OFF
  -DIREE_BUILD_PYTHON_BINDINGS=OFF
  # Compiler: disable non-CPU backends
  -DIREE_TARGET_BACKEND_DEFAULTS=OFF
  -DIREE_TARGET_BACKEND_LLVM_CPU=ON
  -DIREE_TARGET_BACKEND_VMVX=OFF
  # Kernels are plain linalg, compiled for x86 only, so skip the input
  # frontends (StableHLO, torch-mlir, TOSA) and other LLVM CPU targets
  -DIREE_INPUT_STABLEHLO=OFF
  -DIREE_INPUT_TORCH=OFF
  -DIREE_INPUT_TOSA=OFF
  -DIREE_DEFAULT_CPU_LLVM_TARGETS=X86
  # The runtime is not built here, but keep its configuration minimal
  -DIREE_HAL_DRIVER_DEFAULTS=OFF
  -DIREE_HAL_DRIVER_LOCAL_TASK=ON
  -DIREE_HAL_EXECUTABLE_LOADER_DEFAULTS=OFF
  -DIREE_HAL_EXECUTABLE_LOADER_EMBEDDED_ELF=ON
)

cmake "${cmake_args[@]}" "$@"
cmake --build "${build_dir}" \
  --target iree_compiler_API_SharedImpl iree-lld iree-compile

# The compiler links CPU kernels with iree-lld, which it looks for next to
# libIREECompiler.so or in an adjacent bin/. The build tree puts it in tools/.
mkdir -p "${build_dir}/bin"
ln -sf ../tools/iree-lld "${build_dir}/bin/iree-lld"

library="${build_dir}/lib/libIREECompiler.so"
echo "Built ${library}, ${build_dir}/bin/iree-lld and" \
  "${build_dir}/tools/iree-compile"
if [ "${build_dir}" != "${repo_root}/build-iree" ]; then
  echo "Configure monad with -DMONAD_IREE_BUILD_DIR=${build_dir}"
fi
