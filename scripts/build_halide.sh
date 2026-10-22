#!/bin/bash
#
# Builds Halide from third_party/halide, outside the monad build: libHalide.so,
# which holds both the compiler and the runtime that the code it compiles
# links, so the monad build only links it, and the CPU autoscheduler plugins,
# Adams2019, Li2018 and Mullapudi2016, which graph_eval's Halide compiler
# loads from this build at run time to schedule graphs. It's built against the
# system's LLVM 21 (llvm-21-dev, clang-21, libclang-21-dev and liblld-21-dev),
# whose libLLVM.so it then needs at run time, and only needs rebuilding when
# the submodule is bumped.
#
# Environment:
#   HALIDE_BUILD_DIR   build directory (default: <repo>/build-halide)
#   HALIDE_BUILD_TYPE  CMake build type (default: Release)
#   CC, CXX            compilers, as for any CMake project
#
# Extra arguments are passed to the CMake configure step, e.g.
#   scripts/build_halide.sh -DHalide_LLVM_ROOT=/opt/llvm-22

set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
build_dir="$(realpath -m "${HALIDE_BUILD_DIR:-${repo_root}/build-halide}")"

cmake_args=(
  -S "${repo_root}/third_party/halide"
  -B "${build_dir}"
  -G Ninja
  -DCMAKE_BUILD_TYPE:STRING="${HALIDE_BUILD_TYPE:-Release}"
  # Graphs are compiled in-process for x86, so skip the Python bindings and
  # the in-process Wasm JIT, whose wabt dependency no apt package satisfies
  -DWITH_PYTHON_BINDINGS=OFF
  -DHalide_WASM_BACKEND=OFF
  # Pipeline serialization, which needs flatbuffers, isn't used
  -DWITH_SERIALIZATION=OFF
  -DWITH_TESTS=OFF
  -DWITH_TUTORIALS=OFF
  -DWITH_UTILS=OFF
)

cmake "${cmake_args[@]}" "$@"
cmake --build "${build_dir}" \
  --target Halide Halide_Adams2019 Halide_Li2018 Halide_Mullapudi2016

library="${build_dir}/src/libHalide.so"
echo "Built ${library} and the autoscheduler plugins in" \
  "${build_dir}/src/autoschedulers"
if [ "${build_dir}" != "${repo_root}/build-halide" ]; then
  echo "Configure monad with -DMONAD_HALIDE_BUILD_DIR=${build_dir}"
fi
