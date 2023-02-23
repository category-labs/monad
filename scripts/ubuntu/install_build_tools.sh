DEPS="
  clang-14
  clang-tools-14
  cmake
  ninja-build
  python3-pip
"

apt-get -q -o=Dpkg::Use-Pty=0 install ${DEPS}

pip install 'conan<2.0'
