#!/usr/bin/env bash
set -euo pipefail
# Pin the key independently of runtime environment overrides.
key_version=1.3.1-alpha
key_md5=b86c1150b45298ffab2e907f03d0747b
key_root=${KEY_ROOT:-/workspace/keys}
mkdir -p "$key_root"
exec 9>"$key_root/.install.lock"
flock 9
if [[ -f "$key_root/provingKey/.monad-key" ]] && \
   [[ $(cat "$key_root/provingKey/.monad-key") == "$key_version $key_md5" ]]; then
    exit 0
fi
if [[ -e "$key_root/provingKey" ]]; then
    echo "Unrecognized/incomplete key at $key_root/provingKey; choose a fresh KEY_ROOT." >&2
    exit 1
fi
stage=$(mktemp -d "$key_root/.download.XXXXXX")
trap 'rm -rf -- "$stage"' EXIT
archive="zisk-provingkey-$key_version.tar.gz"
curl -fL --retry 5 --connect-timeout 30 \
    "https://storage.googleapis.com/zisk-setup/$archive" -o "$stage/$archive"
(cd "$stage" && printf '%s  %s\n' "$key_md5" "$archive" | md5sum -c -)
tar --no-same-owner -xzf "$stage/$archive" -C "$stage"
test -d "$stage/provingKey"
printf '%s %s\n' "$key_version" "$key_md5" > "$stage/provingKey/.monad-key"
mv "$stage/provingKey" "$key_root/provingKey"
echo "Key installed; the worker generates any missing constant trees on first use."
