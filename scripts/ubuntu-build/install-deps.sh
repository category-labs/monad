#!/bin/bash

packages=(
  libarchive-dev
  libbenchmark-dev
  libbrotli-dev
  libcap-dev
  libcgroup-dev
  libclang-19-dev
  libcli11-dev
  libcrypto++-dev
  libgmock-dev
  libgmp-dev
  libgtest-dev
  libhugetlbfs-dev
  libmagicenum-dev
  libtbb-dev
  liburing-dev
  libzstd-dev
)

apt-get update
apt-get install -y "${packages[@]}"
