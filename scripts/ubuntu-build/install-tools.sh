#!/bin/bash

packages=(
  cmake
  gdb
  ninja-build
  pkg-config
  python3-pytest
  valgrind
)

apt install -y "${packages[@]}"
