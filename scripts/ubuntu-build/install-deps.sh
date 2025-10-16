#!/bin/bash

packages=(
  libarchive-dev
  libbenchmark-dev
  libbrotli-dev
  libcap-dev
  libcgroup-dev
  libcli11-dev
  libcrypto++-dev
  libgmock-dev
  libgmp-dev
  libgtest-dev
  libhugetlbfs-dev
  libtbb-dev
  liburing-dev
  libzstd-dev
)

apt install -y "${packages[@]}"
