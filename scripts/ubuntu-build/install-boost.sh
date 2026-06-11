#!/bin/bash

packages=(
  libboost1.83-dev
  libboost-context1.83.0
  libboost-context1.83-dev
  libboost-filesystem1.83.0
  libboost-filesystem1.83-dev
  libboost-json1.83.0
  libboost-json1.83-dev
  libboost-stacktrace1.83.0
  libboost-stacktrace1.83-dev
  libboost-test1.83.0
  libboost-test1.83-dev
)

apt-get install -y --no-install-recommends "${packages[@]}"
