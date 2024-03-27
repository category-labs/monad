# syntax=docker/dockerfile:1-labs

FROM ubuntu:22.04 as base

RUN apt update

RUN apt upgrade -y

RUN apt install -y apt-utils

RUN apt install -y dialog

RUN apt install -y ca-certificates curl gnupg software-properties-common wget

COPY core/scripts/ubuntu-build/ /opt

RUN /opt/install-gcc.sh
RUN /opt/install-clang.sh
RUN /opt/install-boost.sh
RUN /opt/install-cmake.sh
RUN /opt/install-tools.sh
RUN /opt/install-deps.sh

RUN apt install -y \
 libarchive-dev \
 libcap-dev \
 libcli11-dev \
 libzstd-dev

FROM base as build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} \
   CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" \
   ./core/scripts/configure.sh

RUN cd src && ./core/scripts/build.sh

# Replace the line below with this when you want CI to print exactly where it is hanging at
# RUN cd src && ctest --output-on-failure -V --test-dir build

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && PYTHONPATH="core" CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./core/scripts/test.sh
