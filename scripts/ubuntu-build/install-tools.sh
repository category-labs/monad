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

# Need a newer Rust toolchain than Ubuntu has
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
. "$HOME/.cargo/env"
cargo install bindgen-cli
