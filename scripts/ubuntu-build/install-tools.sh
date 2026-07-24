#!/bin/bash

packages=(
  apt-utils
  ca-certificates
  clang-21
  clang-tools-21
  clang-tidy-21
  cmake
  curl
  dialog
  g++-15
  gcc-15
  gdb
  git
  gnupg
  libclang-common-21-dev
  libclang-rt-21-dev
  llvm-21-dev
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
