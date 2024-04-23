#!/bin/bash

# https://launchpad.net/~ubuntu-toolchain-r/+archive/ubuntu/ppa

add-apt-repository -y ppa:ubuntu-toolchain-r/test

apt-get update

apt-get install -y \
  gcc-13 \
  g++-13
