#!/usr/bin/env python3
"""Fail closed unless an ELF is the audited Monad/ZisK 1.2 profile."""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import shlex
import subprocess


PROFILE = "monad-zkvm-official-v2"
RUNTIME_VERSION = "1.3.1-alpha"
RUNTIME_REVISION = "306a9c934ba4947b1d586d69b67120f8b4c41466"
RUNTIME_SOURCE = (
    "git+https://github.com/0xPolygonHermez/zisk.git?tag=v1.3.1-alpha#"
    + RUNTIME_REVISION
)
EXPECTED_COMPILER = ("GNU", "15.2.0")
EXPECTED_MARCH = "rv64ima_zicsr_zba_zbb_zbs_zbkb"
EXPECTED_MTUNE = "size"
REQUIRED_FLAGS = (
    "-O3",
    "-mabi=lp64",
    "-fno-pic",
    "-mzisk-dma",
    "-funroll-loops",
    "--param=inline-unit-growth=800",
    "--param=large-function-growth=1500",
    "--param=max-inline-insns-auto=200",
    "--param=max-inline-insns-single=800",
    "--param=inline-min-speedup=1",
    "-finline-functions",
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


def flag_values(flags: str) -> dict[str, str | bool]:
    """Normalise GCC options, retaining the last value of each setting."""
    # flags.make also contains defines, includes and comments; inspect CXX_FLAGS.
    make_flags = re.search(r"^CXX_FLAGS\s*=[ \t]*(.*)$", flags, re.MULTILINE)
    if make_flags:
        flags = make_flags.group(1)
    elif re.search(r"^(?:C|CXX)_(?:FLAGS|DEFINES|INCLUDES)\s*=", flags, re.MULTILINE):
        fail("guest flags.make omits CXX_FLAGS")
    try:
        tokens = iter(shlex.split(flags, comments=True))
    except ValueError as exc:
        fail(f"cannot parse compiler flags: {exc}")
    values: dict[str, str | bool] = {}
    for token in tokens:
        if token == "--param":
            token = "--param=" + next(tokens, "")
        if token.startswith("--param="):
            name, separator, value = token[len("--param=") :].partition("=")
            if not name or not separator or not value:
                fail(f"malformed compiler parameter: {token}")
            values[f"--param={name}"] = value
        elif token.startswith("-O"):
            values["-O"] = token[2:] or "1"
        else:
            name, separator, value = token.partition("=")
            if name in ("-fPIC", "-fno-PIC"):
                name = name.lower()
            if name.startswith(("-fno-", "-mno-")):
                values[name[:2] + name[5:]] = False
            else:
                values[name] = value if separator else True
    return values


def check_flags(flags: str, where: str) -> None:
    actual = flag_values(flags)
    expected = flag_values(" ".join(REQUIRED_FLAGS))
    expected.update({"-march": EXPECTED_MARCH, "-mtune": EXPECTED_MTUNE})
    for name, value in expected.items():
        if actual.get(name) != value:
            fail(f"{where} has {name}={actual.get(name)!r}, expected {value!r}")


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
    if features != ["baseline", "zisk-dma"]:
        fail(f"unexpected feature set: {features!r}")

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
    for extension in ("zba", "zbb", "zbs", "zbkb"):
        if extension not in attributes:
            fail(f"ELF attributes omit {extension}")

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
            "elf_attributes": ["zba", "zbb", "zbs", "zbkb"],
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
