# syntax=docker/dockerfile:1-labs

FROM ubuntu:25.10 AS base

RUN apt-get update && apt-get upgrade -y

COPY scripts/ubuntu-build/ /opt

RUN /opt/install-boost.sh
RUN /opt/install-tools.sh
RUN /opt/install-deps.sh

FROM base AS build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG GIT_COMMIT_HASH

ENV GIT_COMMIT_HASH=$GIT_COMMIT_HASH

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./scripts/configure.sh

RUN cd src && ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && if [ "${CMAKE_BUILD_TYPE:?}" != "Debug" ]; then CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh; fi

FROM base AS build_and_test_vm

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh
RUN cd src && cmake build -DMONAD_COMPILER_TESTING=On -DMONAD_COMPILER_LLVM=Off

RUN cd src && ./scripts/vm/build-tests.sh
RUN cd src && ./scripts/vm/test.sh

FROM base AS code_quality

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build           \
  -DMONAD_COMPILER_BENCHMARKS=On  \
  -DMONAD_COMPILER_LLVM=Off       \
  -DMONAD_COMPILER_TESTING=On     \
  -DCMAKE_BUILD_TYPE=Debug        \
  -DCMAKE_C_COMPILER=clang-19     \
  -DCMAKE_CXX_COMPILER=clang++-19 \
  -DUTILS_CLANG_TIDY_AUTO_CONST=On

RUN cd src && cmake --build build -t ConstCorrectnessChecks
RUN cd src && ./scripts/check-clang-tidy.sh

FROM base AS vm_fuzz

RUN apt-get update && apt-get install -y tmux

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build \
  -GNinja \
  -DCMAKE_BUILD_TYPE=Release \
  -DMONAD_COMPILER_LLVM=Off \
  -DMONAD_COMPILER_TESTING=On \
  -DCMAKE_C_COMPILER=clang-19 \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN cd src && cmake --build build -t monad-compiler-fuzzer
RUN cd src && ./scripts/vm/ci-fuzzer.sh

FROM base AS runner
COPY --from=build_and_test /src/build/category/mpt/monad-mpt /usr/local/bin/
COPY --from=build_and_test /src/build/cmd/monad-cli /usr/local/bin/
COPY --from=build_and_test /src/build/cmd/monad /usr/local/bin/
