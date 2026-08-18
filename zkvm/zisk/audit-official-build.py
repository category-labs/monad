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
EXPECTED_FEATURES = [
    "baseline",
    "zisk-dma",
    "keccakf-memo",
    "wide-memory-size",
    "varcode-cache",
    "no-dirty-accounts",
    "no-merge-constraints",
    "jumpdest-precompile",
]
EXPECTED_MARCH = "rv64ima_zicsr_zba_zbb_zbs_zbkb"
EXPECTED_MTUNE = "size"
EXPECTED_INTERPRETER_MTUNE = "generic-ooo"
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


def strip_comments(src: str) -> str:
    """Remove C/C++ comments before inspecting function bodies."""
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2)
            out.append(" ")
            i = n if j < 0 else j + 2
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def delete_overloads(src: str) -> dict[str, str | None]:
    """Map delete signatures to bodies, or None for declarations.

    Normalise parameter names and whitespace before matching overloads.
    """
    src = strip_comments(src)
    found: dict[str, str | None] = {}
    for m in re.finditer(r"operator\s+delete\s*(\[\s*\])?\s*\(", src):
        array = "[]" if m.group(1) else ""
        depth, i, n = 1, m.end(), len(src)
        while i < n and depth:
            depth += (src[i] == "(") - (src[i] == ")")
            i += 1
        if depth:
            fail("unbalanced parameter list after an operator delete")
        params = []
        for p in src[m.end() : i - 1].split(","):
            p = p.strip()
            if not p:
                continue
            # Strip trailing parameter names, preserving types such as size_t.
            p = re.sub(r"(?<=[*&])\s*[A-Za-z_]\w*\s*$", "", p)
            p = re.sub(r"\s+[A-Za-z_]\w*\s*$", "", p)
            params.append(re.sub(r"\s+", "", p))
        key = f"operator delete{array}({','.join(params)})"
        rest = src[i:]
        j = re.match(r"\s*(noexcept\s*)?", rest).end()
        if j < len(rest) and rest[j] == "{":
            depth, k = 1, j + 1
            while k < len(rest) and depth:
                depth += (rest[k] == "{") - (rest[k] == "}")
                k += 1
            if depth:
                fail(f"unbalanced body for {key}")
            found[key] = rest[j + 1 : k - 1]
        else:
            found.setdefault(key, None)
    return found


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


def check_dirty_accounts(build_dir: pathlib.Path, repo: pathlib.Path) -> None:
    option = "MONAD_ZKVM_NO_DIRTY_ACCOUNTS"
    if cache_values(build_dir / "CMakeCache.txt").get(option) != "ON":
        fail(f"matching CMake cache did not enable {option}")
    database = build_dir / "compile_commands.json"
    if not database.is_file():
        fail("compile_commands.json is missing; reconfigure the official build")
    commands = json.loads(database.read_text())
    required = {
        (repo / "category/execution/ethereum/state3/state.cpp").resolve(),
        (repo / "zkvm/guest/execute_witness.cpp").resolve(),
    }
    tracer = (repo / "category/execution/ethereum/trace/state_tracer.cpp").resolve()
    seen = set()
    for entry in commands:
        source = (pathlib.Path(entry["directory"]) / entry["file"]).resolve()
        if source == tracer:
            fail("state_tracer.cpp is compiled despite disabled dirty-account lists")
        if source not in required:
            continue
        args = entry.get("arguments")
        if args is None:
            args = shlex.split(entry["command"])
        # Respect later -D/-U overrides, including their separated spellings.
        enabled = False
        tokens = iter(args)
        for arg in tokens:
            if arg in ("-D", "-U"):
                arg += next(tokens, "")
            if arg == "-U" + option:
                enabled = False
            elif arg.startswith("-D"):
                name, _, value = arg[2:].partition("=")
                if name == option:
                    enabled = value in ("", "1")
        if not enabled:
            fail(f"{source.name} compile command does not enable {option}")
        seen.add(source)
    if seen != required:
        fail("compile commands are missing State or the guest entry point")


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
        "*/build/monad-zkvm-official-profile.json"
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
    guest_text = guest_flags[0].read_text(errors="replace")
    check_flags(guest_text, "guest compile command")
    interpreter_flags = list(build_dir.glob("**/monad-vm-interpreter.dir/flags.make"))
    if len(interpreter_flags) != 1:
        fail(f"expected one interpreter flags.make, found {len(interpreter_flags)}")
    interpreter_text = interpreter_flags[0].read_text(errors="replace")
    interpreter_mtune = flag_values(interpreter_text).get("-mtune")
    if interpreter_mtune != EXPECTED_INTERPRETER_MTUNE:
        fail(
            f"interpreter compile command ends with -mtune={interpreter_mtune!s}, "
            f"expected {EXPECTED_INTERPRETER_MTUNE}"
        )
    if profile.get("interpreter_flags") != f"-mtune={EXPECTED_INTERPRETER_MTUNE}":
        fail("generated profile does not record the interpreter's tune")

    # Check header inclusion and empty definitions: removed calls let the linker
    # discard delete symbols, so the ELF alone cannot validate the const claim.
    if "-include" not in guest_text or "nodelete.hpp" not in guest_text:
        fail("guest compile command omits -include nodelete.hpp")
    libstdcxx = (args.repo / "zkvm" / "core" / "libstdcxx.cpp").read_text(
        errors="replace"
    )
    # Discover overloads from both files so new ones are checked too.
    declared = delete_overloads(
        (args.repo / "zkvm" / "guest" / "nodelete.hpp").read_text(errors="replace")
    )
    defined = delete_overloads(libstdcxx)
    if not declared:
        fail("nodelete.hpp declares no operator delete; the assertion is gone")
    for key, body in sorted(defined.items()):
        if body is not None and body.strip():
            fail(
                f"libstdcxx.cpp defines {key} with a body; nodelete.hpp asserts "
                "the family does nothing"
            )
    for key in sorted(declared):
        if key not in defined or defined[key] is None:
            fail(
                f"nodelete.hpp declares {key} a no-op and libstdcxx.cpp does not "
                "define it; the attribute then speaks for a definition elsewhere"
            )
    libc = strip_comments(
        (args.repo / "zkvm" / "core" / "libc.cpp").read_text(errors="replace")
    )
    free_body = re.search(r"void free\(void \*(\w+)\)\s*\{(.*?)\n\}", libc, re.S)
    if free_body is None or free_body.group(2).split() != [
        f"(void){free_body.group(1)};"
    ]:
        fail(
            "nodelete.hpp declares free a no-op and libc.cpp no longer "
            "defines it so"
        )
    # Check generated build inputs, not a source filename in the CMake text.
    # State separately asserts that reserve-balance tracking is inactive.
    check_dirty_accounts(build_dir, repo)

    nm = compiler.with_name(compiler.name.replace("g++", "nm"))
    if not nm.exists():
        fail(f"nm not found beside compiler: {nm}")
    for line in subprocess.check_output(
        [str(nm), "--print-size", "--defined-only", str(elf)], text=True
    ).splitlines():
        fields = line.split()
        if len(fields) == 4 and (
            fields[3].startswith(("_Zdl", "_Zda")) or fields[3] == "free"
        ):
            if int(fields[1], 16) != 4:
                fail(
                    f"{fields[3]} is {int(fields[1], 16)} bytes; nodelete.hpp "
                    "asserts it is a no-op"
                )

    readelf = compiler.with_name(compiler.name.replace("g++", "readelf"))
    if not readelf.is_file():
        fail(f"readelf not found beside compiler: {readelf}")
    attributes = run(str(readelf), "-A", str(elf))
    for extension in ("zba", "zbb", "zbs", "zbkb"):
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
            "elf_attributes": ["zba", "zbb", "zbs", "zbkb"],
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
