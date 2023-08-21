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
  abseil-cpp \
  abseil-cpp-debuginfo \
  boost-fiber \
  boost-fiber-debuginfo \
  brotli \
  brotli-debuginfo \
  gmock \
  gmock-debuginfo \
  gmp \
  gmp-debuginfo \
  gtest \
  gtest-debuginfo \
  liburing \
  liburing-debuginfo \
  mimalloc \
  mimalloc-debuginfo \
  rocksdb \
  rocksdb-debuginfo \
  valgrind

RUN yum -y install \
  abseil-cpp-devel \
  boost-devel \
  brotli-devel \
  cli11-devel \
  gmock-devel \
  gmp-devel \
  gtest-devel \
  liburing-devel \
  mimalloc-devel \
  rocksdb-devel \
  valgrind-devel

COPY . monad

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG DISABLE_TESTS

RUN cd monad && CC=${CC} CXX=${CXX} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./monad-core/scripts/configure.sh

RUN cd monad && ./monad-core/scripts/build.sh

RUN cd monad && [ "$DISABLE_TESTS" = 1 ] || ./monad-core/scripts/test.sh
