#!/bin/bash

set -euo pipefail

spec="${1:-$(dirname "$0")/../../third_party/monad-execution-specs}"

opam init --bare -n -y
opam update -R
if ! opam switch list --short | grep -x monad-spec > /dev/null; then
    opam switch create monad-spec --empty --no-switch -y
fi
opam install --switch=monad-spec --deps-only -y "${spec}"
