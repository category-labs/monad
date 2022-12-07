#!/bin/bash
DEPS="
  libabsl-dev
  libboost-fiber1.74-dev
  libbrotli-dev
  libcli11-dev
  librocksdb-dev
"

apt-get -q -y -o=Dpkg::Use-Pty=0 install ${DEPS}

