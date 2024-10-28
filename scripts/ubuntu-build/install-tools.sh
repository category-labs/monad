#!/bin/bash

export DEBIAN_FRONTEND=noninteractive

packages=(
  cmake
  gcovr
  gdb
  llvm
  ninja-build
  pkg-config
  python3-pytest
  valgrind
)

apt install -y "${packages[@]}"
