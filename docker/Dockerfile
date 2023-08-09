# docker build -f docker/Dockerfile .

FROM fedora:38

RUN yum -y install \
  dnf-plugins-core

RUN dnf config-manager --enable \
  fedora-debuginfo \
  fedora-modular-debuginfo \
  updates-debuginfo

RUN yum -y update

RUN yum -y install \
  clang \
  cmake \
  git \
  ninja-build \
  python3-pip \
  zip

RUN yum -y install \
  boost-fiber \
  brotli \
  gmp \
  gtest \
  gmock \
  rocksdb

RUN yum -y install \
  boost-devel \
  brotli-devel \
  gmp-devel \
  gtest-devel \
  gmock-devel \
  rocksdb-devel

COPY . monad

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG DISABLE_TESTS

RUN cd monad && CC=${CC} CXX=${CXX} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ./monad-core/scripts/configure.sh

RUN cd monad && ./monad-core/scripts/build.sh

RUN cd monad && [ "$DISABLE_TESTS" = 1 ] || ./monad-core/scripts/test.sh
