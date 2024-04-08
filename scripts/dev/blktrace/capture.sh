#!/bin/bash
if [ "$EUID" -ne 0 ]; then
  echo "Please run me as root"
  exit 1
fi
echo "Capturing five minutes of i/o latencies from $1 ..."
blktrace -d $1 -w 300

