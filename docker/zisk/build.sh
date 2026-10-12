#!/usr/bin/env bash
set -euo pipefail
# Build the guest locally; compile the host client in Docker for runtime ABI compatibility.
# Private Git dependency authentication stays on the host; Docker receives vendored sources.
if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "Usage: $0 MONAD_SOURCE ETHPROOFS_SOURCE [IMAGE_TAG]" >&2
    echo 'Requires Docker, Cargo, the ZisK 1.3.1 toolchain, CMake/Boost and RISCV_TOOLCHAIN_DIR.' >&2
    exit 2
fi
monad=$(realpath "$1")
ethproofs=$(realpath "$2")
image=${3:-ghcr.io/goodlyrottenapple/monad-zisk-prover:1.3.1-alpha}
scripts=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
context=$(mktemp -d "${TMPDIR:-/tmp}/monad-prover-build.XXXXXX")
trap 'rm -rf -- "$context"' EXIT
mkdir -p "$context/ethproofs/.cargo" "$context/zisk" "$context/scripts"
# The library's build.rs cross-compiles and exposes the release guest path.
# cargo check suffices to run build.rs without linking a redundant host application.
cargo check --locked --lib --manifest-path "$monad/zkvm/zisk/Cargo.toml" \
    --message-format=json > "$context/guest-build.jsonl"
python3 - "$context" <<'PY'
import json, shutil, sys
from pathlib import Path
ctx = Path(sys.argv[1])
paths = []
for line in (ctx / 'guest-build.jsonl').read_text().splitlines():
    item = json.loads(line)
    if item.get('reason') == 'build-script-executed':
        paths.extend(value for name, value in item.get('env', []) if name == 'MONAD_GUEST_ELF')
if len(paths) != 1:
    raise SystemExit('Expected one Monad guest ELF from the host library build')
shutil.copy2(paths[0], ctx / 'monad-zkvm-zisk')
PY
curl -fL --retry 3 https://github.com/0xPolygonHermez/zisk/releases/download/v1.3.1-alpha/cargo_zisk_linux_amd64.tar.gz \
    -o "$context/zisk.tar.gz"
printf '%s  %s\n' 13e590784e79a195db7e85465eef75e0820be7148d12f829e478047542aadef8 "$context/zisk.tar.gz" | sha256sum -c -
tar --no-same-owner -xzf "$context/zisk.tar.gz" -C "$context/zisk"
rm "$context/zisk.tar.gz" "$context/guest-build.jsonl"
cp "$ethproofs/"{Cargo.toml,Cargo.lock,build.rs} "$context/ethproofs/"
cp -R "$ethproofs/src" "$context/ethproofs/"
cargo vendor --locked --manifest-path "$ethproofs/Cargo.toml" "$context/ethproofs/vendor" \
    > "$context/ethproofs/.cargo/config.toml"
cp "$scripts/"{check-image.sh,setup-key.sh,prove-folder.sh,witness.py} "$context/scripts/"
revision() {
    if [[ -d "$1/.jj" ]]; then
        jj -R "$1" log --ignore-working-copy --no-graph -r @ -T commit_id
    else
        git -C "$1" rev-parse HEAD
    fi
}
monad_rev=$(revision "$monad")
ethproofs_rev=$(revision "$ethproofs")
python3 - "$context" "$monad_rev" "$ethproofs_rev" <<'PY'
import hashlib, json, sys, tomllib
from pathlib import Path
ctx = Path(sys.argv[1])
config = ctx / 'ethproofs/.cargo/config.toml'
config.write_text(config.read_text().replace(str(ctx / 'ethproofs/vendor'), 'vendor'))
lock = tomllib.loads((ctx / 'ethproofs/Cargo.lock').read_text())
for package in lock['package']:
    if package['name'].startswith(('zisk-', 'proofman-', 'pil2-')) or package['name'] == 'ziskos':
        if package['version'] != '1.3.1-alpha':
            raise SystemExit(f"Unexpected ZisK dependency version: {package['name']} {package['version']}")
manifest = tomllib.loads((ctx / 'ethproofs/Cargo.toml').read_text())
metadata = {
    'zisk': '1.3.1-alpha', 'monad_revision': sys.argv[2], 'ethproofs_revision': sys.argv[3],
    'input_revision': manifest['dependencies']['input']['rev'],
    'guest_sha256': hashlib.sha256((ctx / 'monad-zkvm-zisk').read_bytes()).hexdigest(),
    'ethproofs_lock_sha256': hashlib.sha256((ctx / 'ethproofs/Cargo.lock').read_bytes()).hexdigest(),
}
(ctx / 'versions.json').write_text(json.dumps(metadata, indent=2) + '\n')
PY
docker build --platform linux/amd64 --build-arg "MONAD_REVISION=$monad_rev" \
    --build-arg "BUILD_JOBS=${BUILD_JOBS:-8}" -f "$scripts/Dockerfile" -t "$image" "$context"
echo "Built $image. Test it before docker push."
