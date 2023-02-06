DEPS="
  libabsl20210324
  libboost-fiber1.74.0
  libboost-log1.74.0
  libbrotli1
"

apt-get -q -o=Dpkg::Use-Pty=0 install ${DEPS}

