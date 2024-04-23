#!/bin/bash

packages=(
  gdb
  ninja-build
  pkg-config
  python3-pytest
  valgrind
)

apt install -y "${packages[@]}"
