#!/bin/bash

packages=(
  libbenchmark-dev
  libcgroup-dev
  libgmock-dev
  libgtest-dev
  libhugetlbfs-dev
  libtbb-dev
  liburing-dev
)

apt install -y "${packages[@]}"
