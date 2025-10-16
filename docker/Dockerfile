# syntax=docker/dockerfile:1-labs

FROM ubuntu:25.04 AS base

RUN apt update && apt upgrade -y

COPY scripts/ubuntu-build/ /opt

RUN /opt/install-boost.sh
RUN /opt/install-tools.sh
RUN /opt/install-deps.sh

FROM base AS build_and_test

COPY . src
WORKDIR src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE

RUN CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./scripts/configure.sh

RUN ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh

FROM base AS build_and_test_vm

COPY . src
WORKDIR src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG SKIP_LLVM_TESTS
ARG TOOLCHAIN

RUN CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh
RUN cmake build -DMONAD_COMPILER_TESTING=On -DMONAD_COMPILER_LLVM=On

RUN ./scripts/vm/build-tests.sh
RUN SKIP_LLVM_TESTS=${SKIP_LLVM_TESTS:?} ./scripts/vm/test.sh

FROM base AS code_quality

COPY . src
WORKDIR src

RUN CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build           \
  -DMONAD_COMPILER_BENCHMARKS=On  \
  -DMONAD_COMPILER_LLVM=On        \
  -DMONAD_COMPILER_TESTING=On     \
  -DCMAKE_BUILD_TYPE=Debug        \
  -DCMAKE_C_COMPILER=clang-19     \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN ./scripts/check-clang-tidy.sh

FROM base AS vm_fuzz

RUN apt update && apt install -y tmux

COPY . src
WORKDIR src

RUN CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build \
  -GNinja \
  -DCMAKE_BUILD_TYPE=Release \
  -DMONAD_COMPILER_LLVM=Off \
  -DMONAD_COMPILER_TESTING=On \
  -DCMAKE_C_COMPILER=clang-19 \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN cmake --build build -t monad-compiler-fuzzer
RUN ./scripts/vm/ci-fuzzer.sh
