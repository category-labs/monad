#!/bin/bash

source "$(dirname "$0")/toolchain.env"

packages=(
  libarchive-dev
  libbenchmark-dev
  libbrotli-dev
  libcap-dev
  libclang-${LLVM_VERSION}-dev
  libcli11-dev
  libcrypto++-dev
  libgmock-dev
  libgmp-dev
  libgtest-dev
  libtbb-dev
  liburing-dev
  libzstd-dev
)

apt-get install -y --no-install-recommends "${packages[@]}"
