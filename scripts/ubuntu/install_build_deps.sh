DEPS="
  libabsl-dev
  libboost-fiber1.74-dev
  libbrotli-dev
  libcli11-dev
"

apt-get -q -o=Dpkg::Use-Pty=0 install ${DEPS}

