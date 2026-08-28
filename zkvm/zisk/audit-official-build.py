#!/usr/bin/env python3
"""Fail closed unless an ELF is the audited official Monad ZisK profile."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import struct
import subprocess


MARKER = b"monad-zkvm-official-v1;dma=1;table_arg=1;keccakf_memo=1;fuse=1"
REQUIRED_OPTIONS = {
    "MONAD_ZKVM_OFFICIAL_PROFILE": "ON",
    "MONAD_ZKVM_ZISK_DMA": "ON",
    "MONAD_ZKVM_TABLE_ARG": "ON",
    "MONAD_ZKVM_KECCAKF_MEMO": "ON",
    "MONAD_ZKVM_FUSE": "ON",
    "MONAD_ZKVM_KECCAK_SITES": "OFF",
    "MONAD_ZKVM_SELFTEST": "OFF",
}
REQUIRED_FLAGS = (
    "-O3",
    "-mtune=generic-ooo",
    "-march=rv64ima_zbb_zbs_zbkb_zicsr",
    "-mzisk-dma",
)


def fail(message: str) -> None:
    raise SystemExit(f"official-build audit failed: {message}")


def sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def cache_values(path: pathlib.Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(errors="replace").splitlines():
        if not line or line.startswith(("#", "//")) or "=" not in line:
            continue
        key_type, value = line.split("=", 1)
        values[key_type.split(":", 1)[0]] = value
    return values


def count_csr_words(data: bytes, csr: int) -> int:
    # CSRS csr,rs: CSR in bits 31..20; rs1 varies; funct3=010, opcode=0x73.
    return sum(
        1
        for (word,) in struct.iter_unpack("<I", data[: len(data) & ~3])
        if word & 0xFFF0707F == (csr << 20) | 0x2073
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--elf", required=True, type=pathlib.Path)
    ap.add_argument("--build-root", required=True, type=pathlib.Path)
    ap.add_argument("--repo", required=True, type=pathlib.Path)
    ap.add_argument("--manifest", required=True, type=pathlib.Path)
    args = ap.parse_args()

    elf = args.elf.resolve()
    if not elf.is_file():
        fail("ELF is missing")
    data = elf.read_bytes()
    if MARKER not in data:
        fail("ELF does not contain the official-profile marker")
    commit = subprocess.check_output(
        ["git", "-C", str(args.repo.resolve()), "rev-parse", "HEAD"], text=True
    ).strip()
    candidates = []
    for profile_path in args.build_root.resolve().glob(
        "*/out/build/monad-zkvm-official-profile.json"
    ):
        candidate = json.loads(profile_path.read_text())
        signature = candidate.get("build_signature", "")
        exact_marker = (
            MARKER
            + b";commit="
            + commit.encode()
            + b";signature="
            + signature.encode()
        )
        if candidate.get("commit") == commit and exact_marker in data:
            candidates.append((profile_path.stat().st_mtime_ns, profile_path, candidate))
    if not candidates:
        fail("no generated CMake profile matches the ELF's embedded signature")
    _, profile_path, profile = max(candidates)
    build_dir = profile_path.parent
    cache = build_dir / "CMakeCache.txt"
    if not cache.is_file():
        fail("matching CMake cache is missing")

    cv = cache_values(cache)
    for key, expected in REQUIRED_OPTIONS.items():
        if cv.get(key) != expected:
            fail(f"{key}={cv.get(key)!r}, expected {expected}")

    compiler = pathlib.Path(profile["compiler"])
    if profile.get("schema") != 1:
        fail("unknown generated-profile schema")
    if profile.get("compiler_id") != "GNU" or profile.get("compiler_version") != "15.2.0":
        fail("compiler is not GCC 15.2.0")
    if not compiler.is_file() or sha256(compiler) != profile.get("compiler_sha256"):
        fail("compiler SHA no longer matches the configured compiler")

    effective = " ".join(
        profile.get(key, "")
        for key in ("c_flags", "c_flags_release", "cxx_flags", "cxx_flags_release")
    )
    for flag in REQUIRED_FLAGS:
        if flag not in effective:
            fail(f"effective flags omit {flag}")

    flags_files = list(build_dir.glob("**/flags.make"))
    guest_flags = [p for p in flags_files if "monad-zkvm-guest-zisk.dir" in str(p)]
    if len(guest_flags) != 1:
        fail(f"expected one guest flags.make, found {len(guest_flags)}")
    guest_text = guest_flags[0].read_text(errors="replace")
    for flag in REQUIRED_FLAGS:
        if flag not in guest_text:
            fail(f"guest compile command omits {flag}")

    dma_reads = count_csr_words(data, 0x813)
    dma_writes = count_csr_words(data, 0x816)
    if dma_reads < 10 or dma_writes < 10:
        fail(f"DMA lowering absent or implausibly small ({dma_reads}/{dma_writes})")
    fcall_set = data.count(struct.pack("<I", 0x8C0C5073))
    fcall_get = data.count(struct.pack("<I", 0x8C0CD073))
    if not fcall_set or not fcall_get:
        fail("Keccak memo fcall 24/25 instructions are absent")

    readelf = compiler.with_name(compiler.name.replace("g++", "readelf"))
    if not readelf.exists():
        fail(f"readelf not found beside compiler: {readelf}")
    attrs = subprocess.check_output([str(readelf), "-A", str(elf)], text=True)
    for ext in ("zbb", "zbs", "zbkb"):
        if ext not in attrs:
            fail(f"ELF attributes omit {ext}")

    if profile.get("commit") != commit:
        fail("generated profile commit does not match the checked-out commit")
    signature = profile.get("build_signature", "")
    if len(signature) != 64:
        fail("generated profile has an invalid build signature")
    manifest = {
        "schema": 1,
        "profile": "monad-zkvm-official-v1",
        "commit": commit,
        "elf": str(elf),
        "elf_sha256": sha256(elf),
        "compiler": str(compiler),
        "compiler_sha256": profile["compiler_sha256"],
        "compiler_version": profile["compiler_version"],
        "required_flags": list(REQUIRED_FLAGS),
        "features": {key: True for key in ("dma", "table_arg", "keccakf_memo", "fuse")},
        "evidence": {
            "dma_read_sites": dma_reads,
            "dma_write_sites": dma_writes,
            "keccak_fcall_set_sites": fcall_set,
            "keccak_fcall_get_sites": fcall_get,
            "elf_marker": MARKER.decode(),
        },
    }
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(f"official build OK: {manifest['elf_sha256'][:16]}")
    print(f"manifest: {args.manifest}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, subprocess.CalledProcessError, json.JSONDecodeError) as exc:
        fail(str(exc))
