#!/bin/bash

packages=(
  autoconf
  automake
  autotools-dev
  bc
  bison
  build-essential
  cmake
  curl
  flex
  gawk
  git
  gperf
  libexpat-dev
  libglib2.0-dev
  libgmp-dev
  libmpc-dev
  libmpfr-dev
  libncurses-dev
  libslirp-dev
  libtool
  ninja-build
  patchutils
  python3
  python3-pip
  python3-tomli
  texinfo
  zlib1g-dev
)

apt-get install -y --no-install-recommends "${packages[@]}"
