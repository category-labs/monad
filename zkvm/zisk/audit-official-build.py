#!/usr/bin/env python3
"""Fail closed unless an ELF is the audited Monad/ZisK 1.2 profile."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess


PROFILE = "monad-zkvm-official-v2"
RUNTIME_VERSION = "1.2.0-alpha"
RUNTIME_REVISION = "fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3"
RUNTIME_SOURCE = (
    "git+https://github.com/0xPolygonHermez/zisk.git?tag=v1.2.0-alpha#"
    + RUNTIME_REVISION
)
EXPECTED_COMPILER = ("GNU", "15.2.0")
EXPECTED_FEATURES = ["baseline", "jumpdest-precompile"]
EXPECTED_MARCH = "rv64ima_zicsr_zbb_zbs_zbkb"
EXPECTED_MTUNE = "size"
REQUIRED_FLAGS = (
    "-O3",
    "-mabi=lp64",
    "-fno-pic",
    "-funroll-loops",
    "--param=max-inline-insns-single=1600",
    "--param=max-inline-insns-auto=533",
    "--param=inline-unit-growth=266",
    "--param=max-inline-recursive-depth=6",
    "--param=max-completely-peeled-insns=400",
    "--param=large-function-growth=280",
    "--param=large-unit-insns=30000",
    "-fno-schedule-insns",
    "-fno-schedule-insns2",
    "-fno-jump-tables",
)


def fail(message: str) -> None:
    raise SystemExit(f"official-build audit failed: {message}")


def run(*args: str) -> str:
    return subprocess.check_output(args, text=True).strip()


def sha256(path: pathlib.Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def cache_values(path: pathlib.Path) -> dict[str, str]:
    values: dict[str, str] = {}
    for line in path.read_text(errors="replace").splitlines():
        if not line or line.startswith(("#", "//")) or "=" not in line:
            continue
        key_type, value = line.split("=", 1)
        values[key_type.split(":", 1)[0]] = value
    return values


def last_flag_value(flags: str, name: str) -> str | None:
    matches = re.findall(rf"(?:^|\s){re.escape(name)}=([^\s]+)", flags)
    return matches[-1] if matches else None


def check_flags(flags: str, where: str) -> None:
    for flag in REQUIRED_FLAGS:
        if flag not in flags.split():
            fail(f"{where} omits {flag}")
    march = last_flag_value(flags, "-march")
    if march != EXPECTED_MARCH:
        fail(f"{where} ends with -march={march!s}, expected {EXPECTED_MARCH}")
    mtune = last_flag_value(flags, "-mtune")
    if mtune != EXPECTED_MTUNE:
        fail(f"{where} ends with -mtune={mtune!s}, expected {EXPECTED_MTUNE}")


def check_runtime(repo: pathlib.Path) -> dict[str, str]:
    lock_path = repo / "zkvm/zisk/Cargo.lock"
    packages: list[dict[str, str]] = []
    for stanza in lock_path.read_text().split("[[package]]")[1:]:
        fields = dict(
            re.findall(r'^([a-z]+) = "([^"]*)"$', stanza, flags=re.MULTILINE)
        )
        if fields.get("name") == "ziskos":
            packages.append(fields)
    if len(packages) != 1:
        fail(f"expected one ziskos package in Cargo.lock, found {len(packages)}")
    package = packages[0]
    if package.get("version") != RUNTIME_VERSION:
        fail(f"ziskos version is {package.get('version')!r}, expected {RUNTIME_VERSION}")
    if package.get("source") != RUNTIME_SOURCE:
        fail("ziskos source revision does not match the official profile")
    return {"version": RUNTIME_VERSION, "revision": RUNTIME_REVISION}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--elf", required=True, type=pathlib.Path)
    parser.add_argument("--build-root", required=True, type=pathlib.Path)
    parser.add_argument("--repo", required=True, type=pathlib.Path)
    parser.add_argument("--cargo-zisk", required=True, type=pathlib.Path)
    parser.add_argument("--manifest", required=True, type=pathlib.Path)
    args = parser.parse_args()

    repo = args.repo.resolve()
    elf = args.elf.resolve()
    if not elf.is_file():
        fail("ELF is missing")
    if run("git", "-C", str(repo), "status", "--porcelain", "--untracked-files=normal"):
        fail("worktree changed after the official build")
    commit = run("git", "-C", str(repo), "rev-parse", "HEAD")
    runtime = check_runtime(repo)
    cargo_zisk_version = run(str(args.cargo_zisk), "--version")
    if not cargo_zisk_version.startswith(f"cargo-zisk {RUNTIME_VERSION} "):
        fail(f"cargo-zisk version is not {RUNTIME_VERSION}: {cargo_zisk_version}")

    data = elf.read_bytes()
    candidates: list[tuple[int, pathlib.Path, dict[str, object], bytes]] = []
    for profile_path in args.build_root.resolve().glob(
        "*/out/build/monad-zkvm-official-profile.json"
    ):
        profile = json.loads(profile_path.read_text())
        features = str(profile.get("features_csv", ""))
        signature = str(profile.get("build_signature", ""))
        marker = (
            f"{PROFILE};runtime=ziskos-{RUNTIME_VERSION};features={features};"
            f"commit={commit};signature={signature}"
        ).encode()
        if profile.get("commit") == commit and marker in data:
            candidates.append(
                (profile_path.stat().st_mtime_ns, profile_path, profile, marker)
            )
    if not candidates:
        fail("no generated CMake profile matches the ELF's embedded identity")
    _, profile_path, profile, marker = max(candidates)
    build_dir = profile_path.parent

    if profile.get("schema") != 2 or profile.get("target") != "zisk":
        fail("unknown generated-profile schema or target")
    if profile.get("runtime_version") != RUNTIME_VERSION:
        fail("generated profile has the wrong runtime version")
    if profile.get("runtime_revision") != RUNTIME_REVISION:
        fail("generated profile has the wrong runtime revision")
    features = str(profile.get("features_csv", "")).split(",")
    if features != EXPECTED_FEATURES:
        fail(f"unexpected official feature set: {features!r}")

    cache = build_dir / "CMakeCache.txt"
    if not cache.is_file():
        fail("matching CMake cache is missing")
    values = cache_values(cache)
    if values.get("MONAD_ZKVM_OFFICIAL_PROFILE") != "ON":
        fail("matching CMake cache did not enable the official profile")
    if values.get("MONAD_ZKVM_GUEST_TARGET") != "zisk":
        fail("matching CMake cache is not a ZisK guest build")

    compiler = pathlib.Path(str(profile["compiler"]))
    compiler_id = str(profile.get("compiler_id", ""))
    compiler_version = str(profile.get("compiler_version", ""))
    if (compiler_id, compiler_version) != EXPECTED_COMPILER:
        fail(f"compiler is {compiler_id} {compiler_version}, expected GNU 15.2.0")
    if not compiler.is_file() or sha256(compiler) != profile.get("compiler_sha256"):
        fail("compiler SHA no longer matches the configured compiler")

    effective = " ".join(
        str(profile.get(key, ""))
        for key in ("cxx_flags", "cxx_flags_release")
    )
    check_flags(effective, "generated C++ profile")
    guest_flags = list(build_dir.glob("**/monad-zkvm-guest-zisk.dir/flags.make"))
    if len(guest_flags) != 1:
        fail(f"expected one guest flags.make, found {len(guest_flags)}")
    check_flags(guest_flags[0].read_text(errors="replace"), "guest compile command")

    readelf = compiler.with_name(compiler.name.replace("g++", "readelf"))
    if not readelf.is_file():
        fail(f"readelf not found beside compiler: {readelf}")
    attributes = run(str(readelf), "-A", str(elf))
    for extension in ("zbb", "zbs", "zbkb"):
        if extension not in attributes:
            fail(f"ELF attributes omit {extension}")

    objdump = compiler.with_name(compiler.name.replace("g++", "objdump"))
    if not objdump.is_file():
        fail(f"objdump not found beside compiler: {objdump}")
    disassembly = run(str(objdump), "-d", str(elf))
    jumpdest_syscalls = len(re.findall(r"\bcsrs\s+0x81c,", disassembly))
    if jumpdest_syscalls == 0:
        fail("ELF does not contain the ZisK JUMPDEST syscall")

    signature = str(profile.get("build_signature", ""))
    if len(signature) != 64:
        fail("generated profile has an invalid build signature")
    manifest = {
        "schema": 2,
        "profile": PROFILE,
        "commit": commit,
        "elf": str(elf),
        "elf_sha256": sha256(elf),
        "compiler": str(compiler),
        "compiler_id": compiler_id,
        "compiler_version": compiler_version,
        "compiler_sha256": profile["compiler_sha256"],
        "cargo_zisk_version": cargo_zisk_version,
        "runtime": runtime,
        "features": features,
        "required_flags": list(REQUIRED_FLAGS),
        "effective_flags": effective,
        "evidence": {
            "elf_marker": marker.decode(),
            "elf_attributes": ["zbb", "zbs", "zbkb"],
            "jumpdest_syscalls": jumpdest_syscalls,
            "cargo_lock_sha256": sha256(repo / "zkvm/zisk/Cargo.lock"),
            "cmake_profile_sha256": sha256(profile_path),
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
