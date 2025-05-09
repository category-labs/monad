# syntax=docker/dockerfile:1-labs

FROM ubuntu:24.04 as base

RUN apt update && apt upgrade -y

RUN apt update && apt install -y apt-utils

RUN apt update && apt install -y dialog

RUN apt update && apt install -y \
  ca-certificates \
  curl \
  gnupg \
  software-properties-common \
  wget

RUN add-apt-repository -y ppa:ubuntu-toolchain-r/test
RUN add-apt-repository -y ppa:mhier/libboost-latest

RUN apt update && apt install -y libstdc++-13-dev

RUN apt update && apt install -y \
  libboost-atomic1.83.0 \
  libboost-container1.83.0 \
  libboost-fiber1.83.0 \
  libboost-filesystem1.83.0 \
  libboost-json1.83.0 \
  libboost-regex1.83.0 \
  libboost-stacktrace1.83.0

RUN apt update && apt install -y \
  libarchive-dev \
  libbenchmark-dev \
  libbrotli-dev \
  libcap-dev \
  libcli11-dev \
  libgmock-dev \
  libgmp-dev \
  libgtest-dev \
  libtbb-dev \
  liburing-dev \
  libzstd-dev

RUN apt update && apt install -y \
  gdb \
  git \
  python-is-python3 \
  valgrind

FROM base as build

RUN apt update && apt install -y gcc-14 g++-14

RUN apt update && apt install -y cmake ninja-build pkg-config
RUN apt update && apt install -y python3-pytest

RUN apt update && apt-get install -y \
  libboost-fiber1.83-dev \
  libboost-json1.83-dev \
  libboost-stacktrace1.83-dev \
  libboost1.83-dev \
  libcgroup-dev

COPY . src
WORKDIR src

ARG GIT_COMMIT_HASH
RUN test -n "$GIT_COMMIT_HASH"
ENV GIT_COMMIT_HASH=$GIT_COMMIT_HASH

RUN CC=gcc-14 CXX=g++-14 CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_TOOLCHAIN_FILE:STRING=libs/core/toolchains/temp-strip-release.cmake \
  -DCMAKE_BUILD_TYPE:STRING=Release \
  -B build \
  -G Ninja

RUN VERBOSE=1 cmake \
  --build build \
  --target all

# security=insecure for tests which use io_uring
RUN --security=insecure CC=gcc-14 CXX=g++-14 CMAKE_BUILD_TYPE=Release ./scripts/test.sh

FROM base as runner
COPY --from=build /src/build/libs/db/monad_mpt /usr/local/bin/
COPY --from=build /src/build/cmd/monad_cli /usr/local/bin/
COPY --from=build /src/build/cmd/monad /usr/local/bin/
