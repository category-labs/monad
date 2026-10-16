# Copyright (C) 2025-26 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

"""Configure and build the ZisK archive for both Cargo and build.sh."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys

from toolchain import fingerprint


TARGET = "riscv64ima-zisk-zkvm-elf"
ARCHIVE = "libmonad-zkvm-guest-zisk.a"
# Preserve the flags previously supplied by cmake-rs, including the leading space.
BASE_FLAGS = " -ffunction-sections -fdata-sections -fPIC -march=rv64ima -mabi=lp64 -w"


def env_names(name):
    return [
        name, "TARGET_" + name,
        name + "_" + TARGET.replace("-", "_"), name + "_" + TARGET,
    ]


def compiler_flags(name, env):
    no_defaults = env.get("CRATE_CC_NO_DEFAULTS", "0") not in ("0", "false", "no", "")
    escaped = env.get("CC_SHELL_ESCAPED_FLAGS", "0") not in ("0", "false", "no", "")
    flags = " -w" if no_defaults else BASE_FLAGS
    # cc-rs appends increasingly specific environment flags, then cmake-rs
    # drops optimisation/debug flags so CMake's build type controls them.
    for variable in env_names(name):
        value = env.get(variable, "")
        words = shlex.split(value) if escaped else value.split()
        for word in words:
            if not word.startswith(("-O", "/O")) and word != "-g":
                flags += " " + word
    return flags


def definitions(value):
    words = shlex.split(value)
    result = []
    for word in words:
        if not word.startswith("-D") or "=" not in word[2:]:
            raise ValueError("MONAD_ZKVM_CMAKE_ARGS takes -DNAME=VALUE words")
        name, value = word[2:].split("=", 1)
        # Match build-support's existing treatment of -DNAME:TYPE=VALUE.
        name = name.split(":", 1)[0]
        if not name:
            raise ValueError("empty CMake definition name")
        result.append((name, value))
    return result


def build(repo, env, cargo=False):
    extra = definitions(env.get("MONAD_ZKVM_CMAKE_ARGS", ""))

    if not env.get("RISCV_TOOLCHAIN_DIR"):
        raise ValueError("RISCV_TOOLCHAIN_DIR is not set")
    toolchain = Path(env["RISCV_TOOLCHAIN_DIR"]).absolute()
    compilers = [toolchain / "bin" / (prefix + "gcc") for prefix in
                 ("riscv64-none-elf-", "riscv64-unknown-elf-", "riscv-none-elf-")]
    gcc = next((path for path in compilers if path.is_file()), None)
    if gcc is None:
        raise ValueError(f"no RISC-V GCC under {toolchain}/bin")
    toolchain_key, watched = fingerprint(gcc)
    cflags = compiler_flags("CFLAGS", env)
    cxxflags = compiler_flags("CXXFLAGS", env)
    config = {
        "CMAKE_TOOLCHAIN_FILE": str(repo / "category/core/toolchains/riscv64-elf.cmake"),
        "MONAD_ZKVM_GUEST_TARGET": "zisk",
        "RISCV_TOOLCHAIN_DIR": str(toolchain),
        "CMAKE_BUILD_TYPE": "Release",
        "CMAKE_PREFIX_PATH": env.get("CMAKE_PREFIX_PATH", "/usr"),
        "CMAKE_C_FLAGS": cflags,
        "CMAKE_CXX_FLAGS": cxxflags,
        "CMAKE_ASM_FLAGS": cflags,
        "MONAD_ZKVM_ZISK_DMA": env.get("MONAD_ZKVM_ZISK_DMA", "OFF"),
        "MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES": env.get("MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES", "OFF"),
    }
    config.update(extra)
    generator = env.get("CMAKE_GENERATOR")
    # Include configuration, not the commit stamp, so objects survive rebases.
    # New keys also avoid reusing caches created by the old cmake-rs path.
    key = hashlib.sha256(
        json.dumps([config, generator], sort_keys=True).encode()
    ).hexdigest()
    # Separate caches keep Cargo and standalone builds independently testable.
    cache = "guest-build" if cargo else "cmake"
    root = repo / "zkvm/zisk/target" / cache / f"zisk-{toolchain_key}-{key}"
    directory = root / "build"
    directory.mkdir(parents=True, exist_ok=True)
    # Always supply both stamps so an omitted value cannot survive in CMakeCache.
    config.setdefault("MONAD_ZKVM_GIT_COMMIT", env.get("MONAD_ZKVM_GIT_COMMIT", ""))
    config.setdefault("MONAD_ZKVM_BUILD_ID", env.get("MONAD_ZKVM_BUILD_ID", "none"))
    config.setdefault("CMAKE_INSTALL_PREFIX", str(root))
    cmake = next(
        (env[name] for name in reversed(env_names("CMAKE")) if name in env), "cmake"
    )
    command = [cmake, "-S", str(repo / "zkvm/guest"), "-B", str(directory)]
    if generator:
        command += ["-G", generator]
    command += [f"-D{name}={value}" for name, value in config.items()]
    subprocess.run(command, cwd=directory, env=env, stdout=sys.stderr, check=True)
    command = [cmake, "--build", str(directory), "--target",
               "monad-zkvm-guest-zisk", "--config", "Release"]
    if env.get("NUM_JOBS"):
        command += ["--parallel", env["NUM_JOBS"]]
    elif not env.get("CMAKE_BUILD_PARALLEL_LEVEL"):
        command += ["--parallel"]
    subprocess.run(command, cwd=directory, env=env, stdout=sys.stderr, check=True)
    archive = directory / ARCHIVE
    if not archive.is_file():
        raise FileNotFoundError(archive)
    return archive, watched


# These inputs were previously observed by cmake-rs/cc-rs or toolchain.rs.
WATCH_ENV = [
    "RISCV_TOOLCHAIN_DIR", "MONAD_ZKVM_GIT_COMMIT", "MONAD_ZKVM_BUILD_ID",
    "MONAD_ZKVM_ZISK_DMA", "MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES",
    "MONAD_ZKVM_CMAKE_ARGS", "CMAKE_PREFIX_PATH", "CMAKE_GENERATOR",
    "PATH", "GCC_EXEC_PREFIX", "COMPILER_PATH", "CRATE_CC_NO_DEFAULTS",
    "CC_SHELL_ESCAPED_FLAGS", *env_names("CMAKE"),
    *env_names("CFLAGS"), *env_names("CXXFLAGS"),
]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--cargo", action="store_true", help="use Cargo's cache and report its inputs"
    )
    args = parser.parse_args()
    try:
        archive, watched = build(
            Path(__file__).resolve().parents[2], dict(os.environ), args.cargo
        )
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
    # stdout is a protocol: archive path, then Cargo directives when requested.
    print(archive)
    if args.cargo:
        for path in [Path(__file__), Path(__file__).with_name("toolchain.py"), *watched]:
            print(f"cargo:rerun-if-changed={path}")
        for name in WATCH_ENV:
            print(f"cargo:rerun-if-env-changed={name}")
