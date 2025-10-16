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
  libhugetlbfs-bin
  ninja-build
  pkg-config
  python-is-python3
  python3-pytest
  software-properties-common
  valgrind
  wget
)

apt-get update
apt-get install -y "${packages[@]}"
