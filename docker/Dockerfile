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

ARG GCC_VERSION
ENV CC=gcc-${GCC_VERSION} CXX=g++-${GCC_VERSION}

RUN apt-get update && \
    apt-get install -y gcc rustup && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* && \
    rm -rf /opt

RUN rustup toolchain install 1.91.1 --profile minimal --component clippy
RUN rustup toolchain install nightly-2025-12-09 --profile minimal --component rustfmt
RUN RUSTFLAGS="-C linker=${CC}" cargo install cargo-shear@1.9.1

FROM base AS base_vm_test

RUN apt-get update && \
    apt-get install -y opam && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/* /tmp/* /var/tmp/* && \
    rm -rf /opt

COPY scripts/ubuntu-build/install-ocaml.sh third_party/monad-execution-specs/monad-spec.opam /tmp/ocaml/
RUN /tmp/ocaml/install-ocaml.sh /tmp/ocaml && rm -rf /tmp/ocaml

# Spec test fixture tarballs for test/ethereum_test, fetched in their own
# stage so the layers are cached (keyed on the checksums) and CI does not
# depend on GitHub release downloads succeeding on every run. Keep the URLs
# and checksums in sync with test/ethereum_test/CMakeLists.txt.
FROM scratch AS test_fixtures

ADD --checksum=sha256:3e2b02d49fe903eda4fd8caca5cbf0d139c470e97e1de9a85299b1b034f97099 \
    https://github.com/ethereum/execution-spec-tests/releases/download/v5.4.0/fixtures_develop.tar.gz \
    /fixtures/
ADD --checksum=sha256:a19da286fec086ecd82ce06057e0afa3219d4f28bc1e07a3adffad2e1bd4757e \
    https://github.com/monad-developers/execution-specs/releases/download/tests-monad@v1.3.0/fixtures_monad.tar.gz \
    /fixtures/

# ccache directory from an earlier build: empty here; CI passes in the one its
# last push saved (see compiler-cache in .github/actions/docker-stage).
FROM scratch AS compiler_cache

FROM base AS build_and_test

COPY --from=test_fixtures /fixtures /fixtures
ENV MONAD_TEST_FIXTURES_DIR=/fixtures

COPY --from=compiler_cache / /ccache
ENV CCACHE_DIR=/ccache CMAKE_C_COMPILER_LAUNCHER=ccache CMAKE_CXX_COMPILER_LAUNCHER=ccache

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN
ARG GIT_COMMIT_HASH

ENV GIT_COMMIT_HASH=$GIT_COMMIT_HASH

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh

# Evict what this build did not use, so a saved cache stays one build's size.
RUN cd src && start=$(date +%s) && ccache --zero-stats && ./scripts/build.sh && \
    ccache --evict-older-than "$(( $(date +%s) - start + 1 ))s" && ccache --show-stats

# security=insecure for tests which use io_uring
RUN --security=insecure cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} ./scripts/test.sh

# The cache CI saves after a build_and_test build.
FROM scratch AS build_and_test_compiler_cache
COPY --from=build_and_test /ccache /

FROM base_vm_test AS build_and_test_vm

COPY . src

ARG CC
ARG CXX
ARG CMAKE_BUILD_TYPE
ARG TOOLCHAIN

RUN cd src && CC=${CC:?} CXX=${CXX:?} CMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE:?} CMAKE_TOOLCHAIN_FILE=category/core/toolchains/${TOOLCHAIN:?}.cmake ./scripts/configure.sh
RUN cd src && cmake build -DMONAD_COMPILER_TESTING=On -DMONAD_COMPILER_BENCHMARKS=On

RUN cd src && ./scripts/vm/build-tests.sh
RUN cd src && cmake --build build -t execution-benchmarks vm-micro-benchmarks compile-benchmarks mce
RUN cd src && ./scripts/vm/test.sh

FROM base_rust AS build_and_test_rust

COPY . src

ENV TRIEDB_TARGET="triedb_driver"

RUN cd src/rust && cargo update --workspace --locked
RUN cd src/rust && cargo +nightly-2025-12-09 fmt --all --check
RUN cd src/rust && CC=${CC:?} CXX=${CXX:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" RUSTFLAGS="-C linker=${CC:?}" cargo build --release --all-targets --all-features
RUN cd src/rust && CC=${CC:?} CXX=${CXX:?} CFLAGS="-march=haswell" CXXFLAGS="-march=haswell" ASMFLAGS="-march=haswell" RUSTFLAGS="-C linker=${CC:?}" cargo test  --release --all-targets --all-features

FROM base_vm_test AS code_quality

ARG LLVM_VERSION
ENV CC=clang-${LLVM_VERSION} CXX=clang++-${LLVM_VERSION}

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build  \
  -DCMAKE_BUILD_TYPE=Debug             \
  -DCMAKE_C_COMPILER=$CC               \
  -DCMAKE_CXX_COMPILER=$CXX            \
  -DUTILS_CLANG_TIDY_AUTO_CONST=On     \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=TRUE \
  -DMONAD_COMPILER_BENCHMARKS=On       \
  -DMONAD_COMPILER_TESTING=On          \
  -DMONAD_COMPILER_STATS=On            \
  -DMONAD_COMPILER_HOT_PATH_STATS=On

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

COPY flake.nix flake.lock /nix-src/
COPY nix /nix-src/nix
COPY scripts/ubuntu-build/toolchain.env /nix-src/scripts/ubuntu-build/toolchain.env

# Keep the package definitions and the pinned compiler versions inside the
# flake source during pure evaluation.
RUN git init -q /nix-src && git -C /nix-src add flake.nix flake.lock nix scripts

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
        build "git+file:///nix-src#riscv64-none-elf-toolchain" --out-link /toolchain && \
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

ARG GCC_VERSION
COPY scripts/ubuntu-build/check-riscv-gcc.sh /tmp/check-riscv-gcc.sh
RUN CC=gcc-${GCC_VERSION} /tmp/check-riscv-gcc.sh && rm /tmp/check-riscv-gcc.sh

ENV PATH="/riscv/bin:${PATH}"

WORKDIR /

FROM base_riscv_toolchain AS build_zk

COPY . src

RUN cd src && cmake -B build-zkvm -S zkvm/guest \
    -DCMAKE_TOOLCHAIN_FILE=/src/category/core/toolchains/riscv64-elf.cmake \
    -DRISCV_TOOLCHAIN_DIR=/riscv \
    -DMONAD_ZKVM_GUEST_TARGET=zisk \
    -DCMAKE_BUILD_TYPE=Release
RUN cd src && cmake --build build-zkvm --target monad-zkvm-guest-zisk --parallel

FROM base_vm_test AS vm_fuzz

ARG LLVM_VERSION
ENV CC=clang-${LLVM_VERSION} CXX=clang++-${LLVM_VERSION}

COPY . src

RUN cd src && CMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake cmake -S . -B build \
  -GNinja \
  -DCMAKE_BUILD_TYPE=Release \
  -DMONAD_COMPILER_TESTING=On \
  -DCMAKE_C_COMPILER=$CC \
  -DCMAKE_CXX_COMPILER=$CXX

RUN cd src && cmake --build build -t monad-compiler-fuzzer
ARG FUZZER_BASE_SEED
ARG FUZZER_SECONDS
RUN cd src && ./scripts/vm/fuzz.sh -c 26 -i 5 -s "${FUZZER_BASE_SEED:-143}" -t "${FUZZER_SECONDS:-420}"

FROM base AS runner
COPY --from=build_and_test /src/build/category/mpt/monad-mpt /usr/local/bin/
COPY --from=build_and_test /src/build/cmd/monad-cli /usr/local/bin/
COPY --from=build_and_test /src/build/cmd/monad /usr/local/bin/
