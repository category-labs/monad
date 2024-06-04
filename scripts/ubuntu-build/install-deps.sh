#!/bin/bash

packages=(
  libbenchmark-dev
  libgmock-dev
  libgtest-dev
  libtbb-dev
  liburing-dev
)

apt install -y "${packages[@]}"
