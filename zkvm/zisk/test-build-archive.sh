#!/usr/bin/env bash
# Check that `build.sh --archive` builds the objects the ELF links.
#
#   zkvm/zisk/test-build-archive.sh [-DNAME=VALUE ...]
#
# Both entry points use build_archive.py. Compare the archive Cargo actually
# links with a standalone build to catch differences in their environments.
set -euo pipefail

HERE=$(cd "$(dirname "$0")" && pwd)
archive_path_file=$(mktemp)
trap 'rm -f "$archive_path_file"' EXIT
# A fresh path reruns build.rs even when Cargo reuses the compiled guest.
MONAD_ZKVM_ARCHIVE_PATH_FILE="$archive_path_file" "$HERE/build.sh" "$@" >/dev/null
cargo_archive=$(cat "$archive_path_file")
test -f "$cargo_archive" || {
    echo "Cargo did not report its guest archive" >&2
    exit 1
}
archive=$("$HERE/build.sh" --archive "$@" | tail -1)

python3 - "$archive" "$cargo_archive" <<'PY'
import hashlib, sys

def members(path):
    data = open(path, 'rb').read()
    assert data[:8] == b'!<arch>\n', f'{path} is not an ar archive'
    i, names, out = 8, b'', []
    while i < len(data):
        header = data[i:i + 60]
        name = header[:16].decode().strip()
        size = int(header[48:58])
        body = data[i + 60:i + 60 + size]
        i += 60 + size + (size & 1)
        if name == '//':
            names = body
            continue
        if name == '/':
            continue
        if name.startswith('/'):
            off = int(name[1:])
            name = names[off:names.index(b'\n', off)].decode()
        out.append((name.rstrip('/'), hashlib.sha256(body).hexdigest()))
    return sorted(out)

a, b = members(sys.argv[1]), members(sys.argv[2])
if a == b:
    print(f'OK: {len(a)} objects identical')
    sys.exit(0)
da, db = dict(a), dict(b)
for name in sorted(set(da) | set(db)):
    if da.get(name) != db.get(name):
        print(f'differs: {name}')
print(f'FAIL: {sys.argv[1]} and {sys.argv[2]} differ')
sys.exit(1)
PY
