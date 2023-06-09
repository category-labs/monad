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
  ninja-build \
  python3-pip

RUN yum -y install \
  abseil-cpp \
  boost-fiber \
  boost-log \
  brotli \
  gmp \
  gtest \
  rocksdb

RUN yum -y install \
  abseil-cpp-devel \
  boost-devel \
  brotli-devel \
  gmp-devel \
  gtest-devel \
  rocksdb-devel

RUN pip install -U conan==1.*

COPY . monad

RUN cd monad && ls -al && ./scripts/configure.sh

RUN cd monad && ./scripts/build.sh
