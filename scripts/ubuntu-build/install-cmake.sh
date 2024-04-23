#!/bin/bash

# https://apt.kitware.com/

wget -O - https://apt.kitware.com/keys/kitware-archive-latest.asc 2>/dev/null \
  | gpg --dearmor - \
  | tee /usr/share/keyrings/kitware-archive-keyring.gpg >/dev/null

echo 'deb [signed-by=/usr/share/keyrings/kitware-archive-keyring.gpg] https://apt.kitware.com/ubuntu/ jammy main' \
  | tee /etc/apt/sources.list.d/kitware.list >/dev/null

apt-get update

rm /usr/share/keyrings/kitware-archive-keyring.gpg

apt-get -y install kitware-archive-keyring

apt-get -y install cmake
