# syntax=docker/dockerfile:1-labs

FROM ubuntu:26.04 AS base

# Optional mirror to use instead of the default Ubuntu archive.
ARG UBUNTU_MIRROR
RUN if [ -n "${UBUNTU_MIRROR}" ]; then \
        sed -Ei "s,http://(archive|security)\.ubuntu\.com/ubuntu/?,${UBUNTU_MIRROR},g" \
            /etc/apt/sources.list.d/ubuntu.sources; \
    fi

COPY scripts/ubuntu-build/ /opt

RUN apt-get update && \
    apt-get upgrade -y && \
    /opt/install-boost.sh && \
    /opt/install-tools.sh && \
    /opt/install-deps.sh && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* && \
    rm -rf /opt

FROM base AS base_rust

RUN apt-get update && \
    apt-get install -y gcc rustup && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* && \
    rm -rf /opt

RUN rustup toolchain install 1.91.1 --profile minimal --component clippy
RUN rustup toolchain install nightly-2025-12-09 --profile minimal --component rustfmt
RUN RUSTFLAGS="-C linker=gcc-15" cargo install cargo-shear@1.9.1

FROM base AS build_and_test

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN
ARG GIT_COMMIT_HASH

ENV GIT_COMMIT_HASH=$GIT_COMMIT_HASH

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh -DETHEREUM_TEST_WITNESS=ON

RUN cd src && ./scripts/build.sh

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh

FROM base AS build_and_test_vm

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh
RUN cd src && cmake build -DMONAD_COMPILER_TESTING=On

RUN cd src && ./scripts/vm/build-tests.sh
RUN cd src && ./scripts/vm/test.sh

FROM base_rust AS build_and_test_rust

COPY . src

ARG CC
ARG CXX
ENV TRIEDB_TARGET="triedb_driver"

RUN cd src/rust && cargo update --workspace --locked
RUN cd src/rust && cargo +nightly-2025-12-09 fmt --all --check
RUN cd src/rust && CC=${CC:?} CXX=${CXX:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" RUSTFLAGS="-C linker=${CC:?}" cargo build --release --all-targets --all-features
RUN cd src/rust && CC=${CC:?} CXX=${CXX:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" RUSTFLAGS="-C linker=${CC:?}" cargo test  --release --all-targets --all-features

FROM base AS code_quality

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build           \
  -DMONAD_COMPILER_BENCHMARKS=On  \
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
RUN cd src/rust && cargo doc --all-features --no-deps
RUN cd src/rust && cargo test --release --doc --all-features

# nixos/nix:2.35.1 — pinned by digest; keep the tag in this comment in sync
FROM nixos/nix@sha256:377d4887aca98f0dfa12971c1ea6d6a625a435d8b610d4c95a436843da6fbfd1 AS riscv_toolchain_nix

COPY nix /nix-src

# Garbage-collect the build-time closure (GCC sources, stdenv, the stage-1
# compiler) in the same RUN: a later RUN cannot reclaim it, because the bytes
# are already committed to this layer. This takes the store from ~3.6 GB to
# roughly the runtime closure. --out-link registers a GC root so the
# toolchain survives; nix's own paths are rooted by the default profile.
#
# The store path is read back from that symlink rather than from
# --print-out-paths, which prints one line per derivation output and would
# leave /toolchain-path unusable if the toolchain ever grew a second output.
RUN nix --extra-experimental-features "nix-command flakes" \
        build /nix-src#toolchainEnv --out-link /toolchain && \
    readlink -f /toolchain > /toolchain-path && \
    nix-collect-garbage > /dev/null

FROM base AS base_riscv_toolchain

# The toolchain sits at a hash-named store path that moves whenever the pin
# does, so resolve it into a stable /riscv symlink here rather than baking
# the path into this file. The absolute symlink targets inside the store
# resolve because the store is copied to the same absolute location.
COPY --from=riscv_toolchain_nix /nix/store /nix/store
COPY --from=riscv_toolchain_nix /toolchain-path /tmp/toolchain-path
RUN ln -s "$(cat /tmp/toolchain-path)" /riscv && rm /tmp/toolchain-path

COPY scripts/ubuntu-build/check-riscv-gcc.sh /tmp/check-riscv-gcc.sh
RUN /tmp/check-riscv-gcc.sh && rm /tmp/check-riscv-gcc.sh

ENV PATH="/riscv/bin:${PATH}"

WORKDIR /

FROM base_riscv_toolchain AS build_zk

COPY . src

RUN cd src && cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE=/src/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=/riscv \
    -DCMAKE_BUILD_TYPE=Release
RUN cd src && cmake --build build-zkvm --target monad-zkvm --parallel

FROM base AS vm_fuzz

RUN apt-get update && apt-get install -y tmux

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build \
  -GNinja \
  -DCMAKE_BUILD_TYPE=Release \
  -DMONAD_COMPILER_TESTING=On \
  -DCMAKE_C_COMPILER=clang-19 \
  -DCMAKE_CXX_COMPILER=clang++-19

RUN cd src && cmake --build build -t monad-compiler-fuzzer
RUN cd src && ./scripts/vm/ci-fuzzer.sh

FROM base AS runner
COPY --from=build_and_test /src/build/category/mpt/monad-mpt /usr/local/bin/
COPY --from=build_and_test /src/build/cmd/monad-cli /usr/local/bin/
COPY --from=build_and_test /src/build/cmd/monad /usr/local/bin/
