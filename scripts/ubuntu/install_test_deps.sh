#!/bin/bash
DEPS="
  gdb
  libbenchmark-dev
  libgtest-dev
  python3-pytest
  valgrind
"

apt-get -q -y -o=Dpkg::Use-Pty=0 install ${DEPS}

