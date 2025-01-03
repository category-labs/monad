# syntax=docker/dockerfile:1-labs

FROM ubuntu:24.04 as base

RUN apt update &&       \
    apt upgrade -y  &&  \
    apt install -y               \
      apt-utils                  \
      ca-certificates            \
      clang-18                   \
      curl                       \
      dialog                     \
      g++-13                     \
      gcc-13                     \
      gnupg                      \
      libarchive-dev             \
      libbrotli-dev              \
      libcap-dev                 \
      libcli11-dev               \
      libgmp-dev                 \
      libtbb-dev                 \
      libzstd-dev                \
      software-properties-common \
      wget

COPY scripts/ubuntu-build/ /opt
RUN apt update &&          \
  /opt/install-boost.sh && \
  /opt/install-tools.sh && \
  /opt/install-deps.sh

FROM base as build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./scripts/configure.sh

RUN cd src && ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh
