#!/bin/bash

packages=(
  libboost1.90-dev
  libboost-context1.90.0
  libboost-context1.90-dev
  libboost-filesystem1.90.0
  libboost-filesystem1.90-dev
  libboost-json1.90.0
  libboost-json1.90-dev
  libboost-stacktrace1.90.0
  libboost-stacktrace1.90-dev
  libboost-test1.90.0
  libboost-test1.90-dev
)

apt-get install -y --no-install-recommends "${packages[@]}"
