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

COPY scripts/ubuntu-build/ /opt

RUN apt update && apt install -y \
  clang-19 \
  gcc-14 \
  g++-14

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

FROM base as build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./scripts/configure.sh

RUN cd src && ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh
