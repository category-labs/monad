#!/bin/bash

packages=(
  libarchive-dev
  libbenchmark-dev
  libbrotli-dev
  libcap-dev
  libcgroup-dev
  libclang-21-dev
  libcli11-dev
  libcrypto++-dev
  libgmock-dev
  libgmp-dev
  libgtest-dev
  libtbb-dev
  liburing-dev
  libzstd-dev
)

apt-get install -y --no-install-recommends "${packages[@]}"
