#!/bin/bash

packages=(
  clang-tools-19
  clang-tidy-19
  cmake
  gdb
  git
  libhugetlbfs-bin
  ninja-build
  pkg-config
  python-is-python3
  python3-pytest
  valgrind
)

apt install -y "${packages[@]}"
