#!/bin/bash

echo 4 > /sys/devices/system/node/node${1}/hugepages/hugepages-1048576kB/nr_hugepages
echo 2000 > /sys/devices/system/node/node${1}/hugepages/hugepages-2048kB/nr_hugepages
