#!/bin/bash

packages=(
  cmake
  gdb
  git
  ninja-build
  pkg-config
  python-is-python3
  python3-pytest
  valgrind
)

apt install -y "${packages[@]}"
