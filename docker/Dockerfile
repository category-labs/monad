# docker build -f docker/Dockerfile .

FROM fedora:38

RUN --mount=target=monad monad/monad-core/scripts/fedora/enable_debug.sh

RUN yum -y update

RUN --mount=target=monad monad/monad-core/scripts/fedora/install_tools.sh

RUN --mount=target=monad monad/monad-core/scripts/fedora/install_deps.sh

RUN yum -y install \
  brotli \
  brotli-debuginfo \
  gmp \
  gmp-debuginfo \
  rocksdb \
  rocksdb-debuginfo

RUN --mount=target=monad monad/monad-core/scripts/fedora/install_devel.sh

RUN yum -y install \
  brotli-devel \
  cli11-devel \
  gmp-devel \
  rocksdb-devel

COPY . monad

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG DISABLE_TESTS

RUN cd monad && CC=${CC} CXX=${CXX} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" ./monad-core/scripts/configure.sh

RUN cd monad && ./monad-core/scripts/build.sh

RUN cd monad && [ "$DISABLE_TESTS" = 1 ] || ./monad-core/scripts/test.sh
