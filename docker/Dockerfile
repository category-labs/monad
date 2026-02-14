# syntax=docker/dockerfile:1-labs

FROM ubuntu:25.10 AS base

RUN apt-get update && apt-get upgrade -y

COPY scripts/ubuntu-build/ /opt

RUN /opt/install-boost.sh
RUN /opt/install-tools.sh
RUN /opt/install-deps.sh

FROM base AS base_rust

RUN apt-get install -y rustup
RUN rustup toolchain install 1.91.1
RUN rustup toolchain install nightly-2025-12-09
RUN cargo install cargo-shear@1.9.1

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

FROM base_rust AS build_and_test_rust

COPY . src

ARG CC
ARG CXX
ENV TRIEDB_TARGET="triedb_driver"

RUN cd src/rust && cargo update --workspace --locked
RUN cd src/rust && cargo +nightly-2025-12-09 fmt --all --check
RUN cd src/rust && CC=${CC:?} CXX=${CXX:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" cargo build --release --all-targets --all-features
RUN cd src/rust && CC=${CC:?} CXX=${CXX:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" cargo test  --release --all-targets --all-features

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

FROM base_rust AS code_quality_rust

COPY . src

RUN cd src/rust && cargo shear
RUN cd src/rust && cargo clippy --all-targets --all-features -- \
    -D clippy::suspicious \
    -D clippy::style \
    -D clippy::clone_on_copy \
    -D clippy::redundant_clone \
    -D clippy::iter_kv_map \
    -D clippy::iter_nth \
    -D clippy::unnecessary_cast \
    -D clippy::filter_next \
    -D clippy::needless_lifetimes \
    -D clippy::useless_conversion \
    -D clippy::useless_vec \
    -D clippy::needless_question_mark \
    -D clippy::bool_comparison \
    -D unused_imports \
    -D unused_parens \
    -D deprecated \
    -A clippy::type_complexity \
    -A clippy::int_plus_one \
    -A clippy::uninlined-format-args \
    -A clippy::enum-variant-names \
    -A clippy::mutable_key_type \
    -A clippy::large_enum_variant \
    -A clippy::doc-overindented-list-items
RUN cd src/rust && cargo check --all-targets --all-features
RUN cd src/rust && cargo doc
RUN cd src/rust && cargo test --release --doc --all-features

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
