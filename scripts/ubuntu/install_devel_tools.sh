#!/bin/bash
DEPS="
  bpfcc-tools
  gdb
  linux-tools
  ltrace
  strace
  sysstat
  valgrind
"

apt-get -q -y -o=Dpkg::Use-Pty=0 install ${DEPS}

