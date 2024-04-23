#!/bin/bash

### general

apt-get update

apt-get install -y apt-utils

apt-get install -y dialog

apt-get install -y \
  ca-certificates \
  curl \
  gnupg \
  software-properties-common

### docker

# https://docs.docker.com/engine/install/ubuntu/#install-using-the-repository

curl -fsSL https://download.docker.com/linux/ubuntu/gpg \
  | gpg --dearmor -o /etc/apt/keyrings/docker.gpg

chmod a+r /etc/apt/keyrings/docker.gpg

echo \
  "deb [arch="$(dpkg --print-architecture)" \
signed-by=/etc/apt/keyrings/docker.gpg] \
https://download.docker.com/linux/ubuntu \
"$(. /etc/os-release && echo "$VERSION_CODENAME")" stable" \
  | tee /etc/apt/sources.list.d/docker.list > /dev/null

apt-get update

apt-get install -y \
  docker-ce \
  docker-ce-cli \
  docker-ce-rootless-extras \
  containerd.io \
  docker-buildx-plugin \
  docker-compose-plugin

### docker rootless

# https://docs.docker.com/engine/security/rootless/

apt-get install -y \
  uidmap \
  dbus-user-session

systemctl disable --now docker.service docker.socket

### general

apt-get upgrade -y
