#!/bin/bash

source "$(dirname "$0")/toolchain.env"

packages=(
  apt-utils
  ca-certificates
  clang-${LLVM_VERSION}
  clang-tools-${LLVM_VERSION}
  clang-tidy-${LLVM_VERSION}
  cmake
  curl
  dialog
  g++-${GCC_VERSION}
  gcc-${GCC_VERSION}
  gdb
  git
  gnupg
  libclang-common-${LLVM_VERSION}-dev
  libclang-rt-${LLVM_VERSION}-dev
  llvm-${LLVM_VERSION}-dev
  make
  ninja-build
  pkg-config
  python-is-python3
  python3-pytest
  ripgrep
  software-properties-common
  valgrind
  wget
)

apt-get install -y --no-install-recommends "${packages[@]}"
