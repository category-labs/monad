#!/usr/bin/env bash
set -euo pipefail
for binary in /usr/local/bin/ethproofs-client /opt/zisk/bin/{cargo-zisk-cpu,zisk-coordinator,zisk-worker-cpu,zisk-worker-gpu,ziskemu}; do
    if ldd "$binary" | grep -q 'not found'; then
        ldd "$binary" >&2
        exit 1
    fi
    "$binary" --help >/dev/null
done
ethproofs-client --help | grep -q monad
zisk-coordinator --version | grep -q '1.3.1-alpha'
