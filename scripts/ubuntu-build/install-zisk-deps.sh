#!/bin/bash

packages=(
  build-essential
  clang
  curl
  jq
  libclang-dev
  libgmp-dev
  libgrpc++-dev
  libomp-dev
  libopenmpi-dev
  libpqxx-dev
  libsecp256k1-dev
  libsodium-dev
  nasm
  nlohmann-json3-dev
  openmpi-bin
  openmpi-common
  protobuf-compiler
  qemu-system
  uuid-dev
  xz-utils
)

apt-get install -y --no-install-recommends "${packages[@]}"
