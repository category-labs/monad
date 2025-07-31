# syntax=docker/dockerfile:1-labs

FROM ubuntu:25.04 AS base

RUN apt update && apt upgrade -y

RUN apt update && apt install -y apt-utils

RUN apt update && apt install -y dialog

RUN apt update && apt install -y \
  ca-certificates \
  curl \
  gnupg \
  software-properties-common \
  wget

COPY scripts/ubuntu-build/ /opt

RUN apt update && apt install -y \
  clang-19 \
  gcc-15 \
  g++-15

RUN /opt/install-boost.sh
RUN /opt/install-tools.sh
RUN /opt/install-deps.sh

RUN apt update && apt install -y \
  libarchive-dev \
  libbrotli-dev \
  libcap-dev \
  libcli11-dev \
  libgmp-dev \
  libtbb-dev \
  libzstd-dev

FROM base AS build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./scripts/configure.sh

RUN cd src && ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh

FROM base AS build_and_test_vm

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh
RUN cd src && cmake build -DMONAD_COMPILER_TESTING=On

RUN cd src && ./scripts/build-vm-tests.sh
RUN cd src && ./scripts/test-vm.sh

FROM base AS vm_code_quality

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build           \
  -DMONAD_COMPILER_LLVM=On        \
  -DMONAD_COMPILER_TESTING=On     \
  -DCMAKE_C_COMPILER=clang-19     \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN cd src && ./scripts/check-vm-clang-tidy.sh

FROM base AS vm_fuzz

RUN apt update && apt install -y tmux

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build \
  -GNinja \
  -DCMAKE_BUILD_TYPE=Release \
  -DMONAD_COMPILER_LLVM=Off \
  -DMONAD_COMPILER_TESTING=On \
  -DCMAKE_C_COMPILER=clang-19 \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN cd src && cmake --build build -t monad-compiler-fuzzer
RUN cd src && ./scripts/ci-fuzzer.sh