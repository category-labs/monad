#!/bin/bash

packages=(
  apt-utils
  ca-certificates
  clang-19
  clang-tools-19
  clang-tidy-19
  cmake
  curl
  dialog
  g++-15
  gcc-15
  gdb
  git
  gnupg
  libclang-common-19-dev
  libclang-rt-19-dev
  libhugetlbfs-bin
  llvm-19-dev
  make
  ninja-build
  pkg-config
  python-is-python3
  python3-pytest
  software-properties-common
  valgrind
  wget
)

apt-get install -y --no-install-recommends "${packages[@]}"
