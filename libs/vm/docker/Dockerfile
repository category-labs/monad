# syntax=docker/dockerfile:1-labs

#
# Base Image
#

FROM ubuntu:25.04 AS base

RUN apt update && apt upgrade -y

RUN apt update && apt install -y  \
  build-essential                 \
  clang-19                        \
  clang-tools-19                  \
  clang-tidy-19                   \
  cmake                           \
  gcc-15                          \
  g++-15                          \
  git                             \
  libtbb-dev                      \
  libbenchmark-dev                \
  libcli11-dev                    \
  libgmock-dev                    \
  libgtest-dev                    \
  ninja-build                     \
  valgrind

#
# Tests
#

FROM base AS build_and_test

COPY . /src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN

WORKDIR /src

RUN cmake -S . -B build                                         \
  -G Ninja                                                      \
  -DCMAKE_TOOLCHAIN_FILE=cmake/toolchains/${TOOLCHAIN:?}.cmake  \
  -DCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?}                      \
  -DMONAD_COMPILER_BENCHMARKS=On                                \
  -DMONAD_COMPILER_TESTING=On                                   \
  -DMONAD_COMPILER_LLVM=On                                      \
  -DCMAKE_C_COMPILER=${CC:?}                                    \
  -DCMAKE_CXX_COMPILER=${CXX:?}

RUN cmake --build build

RUN ./scripts/ci-tests.sh

#
# Code Quality
#

FROM base AS code_quality

COPY . /src

WORKDIR /src

RUN cmake -S . -B build           \
  -DMONAD_COMPILER_LLVM=On        \
  -DCMAKE_C_COMPILER=clang-19     \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN ./scripts/check-clang-tidy.sh