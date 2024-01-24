# docker build -f docker/Dockerfile .

FROM ubuntu:22.04 as base

RUN apt update

RUN apt upgrade -y

RUN apt install -y apt-utils

RUN apt install -y dialog

RUN apt install -y ca-certificates curl gnupg software-properties-common wget

COPY monad-core/scripts/ubuntu-build/ /opt

RUN /opt/install-gcc.sh
RUN /opt/install-clang.sh
RUN /opt/install-boost.sh
RUN /opt/install-cmake.sh
RUN /opt/install-tools.sh
RUN /opt/install-deps.sh

RUN apt install -y \
  libbrotli-dev \
  libcli11-dev \
  libgmp-dev \
  libtbb-dev

FROM base as build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG DISABLE_TESTS

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./monad-core/scripts/configure.sh

RUN cd src && ./monad-core/scripts/build.sh

RUN cd src && [ "$DISABLE_TESTS" = 1 ] || ./monad-core/scripts/test.sh
