#!/bin/bash

packages=(
  libabsl-dev
  libbenchmark-dev
  libgmock-dev
  libgtest-dev
  libmimalloc-dev
  libtbb-dev
  liburing-dev
)

apt install -y "${packages[@]}"
