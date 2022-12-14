DEPS="
  bpfcc-tools
  gdb
  linux-tools
  ltrace
  strace
  sysstat
  valgrind
"

apt-get -q -o=Dpkg::Use-Pty=0 install ${DEPS}

