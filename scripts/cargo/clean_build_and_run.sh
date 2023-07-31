#!/bin/bash

set -Eeuo pipefail

source "$HOME/.cargo/env"

cargo clean
cargo build
cargo run
