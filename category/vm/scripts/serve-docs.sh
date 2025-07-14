#!/usr/bin/env bash

ROOT_DIR="$(realpath $(dirname "$0")/..)"

doxygen "$ROOT_DIR/Doxyfile"

python3                     \
    -m http.server          \
    --directory docs/html   \
    --bind localhost 8000