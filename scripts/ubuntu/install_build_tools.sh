DEPS="
  clang-14
  clang-tools-14
  cmake
  ninja-build
"

apt-get -q -o=Dpkg::Use-Pty=0 install ${DEPS}

