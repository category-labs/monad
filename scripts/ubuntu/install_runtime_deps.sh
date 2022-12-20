DEPS="
  libabsl20210324
  libboost-fiber1.74.0
  libbrotli1
  librocksdb6.11
"

apt-get -q -o=Dpkg::Use-Pty=0 install ${DEPS}

