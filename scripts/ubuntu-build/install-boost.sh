#!/bin/bash

apt-get update

apt-get install -y \
  libboost-fiber1.83.0 \
  libboost-json1.83.0 \
  libboost-stacktrace1.83.0

apt-get install -y \
  libboost-fiber1.83-dev \
  libboost-json1.83-dev \
  libboost-stacktrace1.83-dev \
  libboost1.83-dev
