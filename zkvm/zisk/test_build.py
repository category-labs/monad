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

"""Exercise the build wrappers without compiling the guest."""

import json
import os
from pathlib import Path
import shutil
import shlex
import sys
import subprocess
import tempfile
import unittest


def archive(path, content):
    path.parent.mkdir(parents=True, exist_ok=True)
    header = f'{"probe.o/":<16}{0:<12}{0:<6}{0:<6}{"100644":<8}{len(content):<10}`\n'
    path.write_bytes(
        b"!<arch>\n" + header.encode() + content + b"\n" * (len(content) % 2)
    )


class BuildTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="monad-build-")
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / "repo with spaces"
        self.here = self.root / "zkvm/zisk"
        self.here.mkdir(parents=True)
        source = Path(__file__).resolve().parent
        for name in ("build.sh", "test-build-archive.sh"):
            shutil.copy2(source / name, self.here / name)
        support = self.root / "zkvm/build-support"
        support.mkdir()
        for name in ("toolchain.py", "build_archive.py"):
            shutil.copy2(source.parent / "build-support" / name, support)

        self.bin = self.root / "bin"
        self.bin.mkdir()
        self.env = dict(os.environ, PATH=f"{self.bin}:{os.environ['PATH']}")
        self.env.pop("MONAD_ZKVM_OFFICIAL_PROFILE", None)
        self.env.pop("MONAD_ZKVM_CMAKE_ARGS", None)
        self.env["RISCV_TOOLCHAIN_DIR"] = str(self.root / "toolchain")
        tc = self.root / "toolchain/bin"
        tc.mkdir(parents=True)
        for name in ("cc1", "cc1plus", "as", "ar", "ranlib"):
            (tc / name).write_text("version 1")
        for name in ("gcc", "g++"):
            self.script(
                tc / f"riscv64-none-elf-{name}",
                '#!/bin/sh\nprintf "%s/%s\\n" "$(dirname "$0")" "${1#-print-prog-name=}"\n',
            )
        for name in ("ar", "ranlib"):
            (tc / f"riscv64-none-elf-{name}").symlink_to(tc / name)
        self.script(
            self.bin / "git",
            '#!/bin/sh\ncase "$*" in *rev-parse*) printf "%040d\\n" 1;; esac\n',
        )

        self.expected = self.root / "expected.a"
        archive(self.expected, b"A")
        self.env["EXPECTED_ARCHIVE"] = str(self.expected)
        self.script(self.bin / "cmake", '''#!/usr/bin/env python3
import json, os, pathlib, shutil, sys
if sys.argv[1] == "--build":
    out = pathlib.Path(sys.argv[2]) / "libmonad-zkvm-guest-zisk.a"
    out.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(os.environ["EXPECTED_ARCHIVE"], out)
else:
    out = pathlib.Path(sys.argv[sys.argv.index("-B") + 1]) / "configure.json"
    out.write_text(json.dumps(sys.argv[1:]))
''')
        self.script(self.bin / "cargo-zisk", '''#!/usr/bin/env python3
import json, os, pathlib, shlex
pathlib.Path("args.json").write_text(json.dumps(shlex.split(os.environ["MONAD_ZKVM_CMAKE_ARGS"])))
elf = pathlib.Path("target/elf/riscv64ima-zisk-zkvm-elf/release/monad-zkvm-zisk")
elf.parent.mkdir(parents=True, exist_ok=True)
elf.touch()
if "MONAD_ZKVM_ARCHIVE_PATH_FILE" in os.environ:
    pathlib.Path(os.environ["MONAD_ZKVM_ARCHIVE_PATH_FILE"]).write_text(os.environ["GUEST_ARCHIVE"])
''')
        self.env["CARGO_ZISK"] = str(self.bin / "cargo-zisk")

    @staticmethod
    def script(path, text):
        path.write_text(text)
        path.chmod(0o755)

    def run_script(self, name, *args):
        return subprocess.run(
            ["bash", str(self.here / name), *args],
            env=self.env,
            capture_output=True,
            text=True,
        )

    def archive_path(self, *args):
        result = self.run_script("build.sh", "--archive", *args)
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout.strip().splitlines()[-1]

    def test_archive_cache_tracks_compiler_frontends(self):
        for args in ((), ("--official",)):
            with self.subTest(args=args):
                first = self.archive_path(*args)
                self.assertEqual(first, self.archive_path(*args))
                with (self.root / "toolchain/bin/cc1plus").open("a") as frontend:
                    frontend.write("rebuild")
                self.assertNotEqual(first, self.archive_path(*args))

    def test_elf_options_preserve_spaces_quotes_and_newlines(self):
        args = [
            "-DCMAKE_CXX_FLAGS=-O2 -g", "-DPATH=/tmp/a b",
            "-DNOTE=it's \\\"quoted\\\"\nnext", "-DEMPTY=",
        ]
        result = self.run_script("build.sh", *args)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads((self.here / "args.json").read_text()), args)

    def test_archive_cache_preserves_definition_boundaries(self):
        self.assertNotEqual(
            self.archive_path("-DFOO=a\n-DBAR=b"),
            self.archive_path("-DFOO=a", "-DBAR=b"),
        )

    def run_helper(self, **variables):
        helper = self.root / "zkvm/build-support/build_archive.py"
        return subprocess.run(
            [sys.executable, str(helper), "--cargo"],
            env=dict(self.env, **variables), capture_output=True, text=True,
        )

    @staticmethod
    def configuration(archive):
        args = json.loads(Path(archive).with_name("configure.json").read_text())
        return dict(arg[2:].split("=", 1) for arg in args if arg.startswith("-D"))

    def test_cargo_and_standalone_share_configuration(self):
        args = ["-DCMAKE_CXX_FLAGS=-O2 -g", "-DNOTE:STRING=it's quoted\nnext"]
        standalone = self.archive_path(*args)
        cargo = self.run_helper(MONAD_ZKVM_CMAKE_ARGS=shlex.join(args))
        self.assertEqual(cargo.returncode, 0, cargo.stderr)
        lines = cargo.stdout.splitlines()
        self.assertNotEqual(standalone, lines[0])
        a, b = self.configuration(standalone), self.configuration(lines[0])
        # Separate caches allow independent builds; the configuration is shared.
        del a["CMAKE_INSTALL_PREFIX"], b["CMAKE_INSTALL_PREFIX"]
        self.assertEqual(a, b)
        self.assertEqual(a["CMAKE_CXX_FLAGS"], "-O2 -g")
        self.assertEqual(a["NOTE"], "it's quoted\nnext")
        for path in ("zkvm/build-support/build_archive.py", "toolchain/bin/cc1plus"):
            self.assertIn(f"cargo:rerun-if-changed={self.root}/{path}", lines)
        self.assertIn(
            "cargo:rerun-if-env-changed=CXXFLAGS_riscv64ima_zisk_zkvm_elf", lines
        )

    def test_environment_flags_and_prefix_invalidate_cache(self):
        before = self.archive_path()
        self.env["CFLAGS"] = "-O2 -g -DBASE=1"
        self.env["TARGET_CFLAGS"] = "-DBASE=2"
        self.env["CFLAGS_riscv64ima_zisk_zkvm_elf"] = "-DBASE=3"
        after = self.archive_path()
        self.assertNotEqual(before, after)
        flags = self.configuration(after)["CMAKE_C_FLAGS"]
        self.assertTrue(flags.endswith(" -w -DBASE=1 -DBASE=2 -DBASE=3"))
        self.assertNotIn("-O2", flags)
        self.assertNotIn(" -g", flags)
        self.env["CMAKE_PREFIX_PATH"] = "/a different Boost"
        self.assertNotEqual(after, self.archive_path())

    def test_official_checks_apply_to_direct_cargo_calls(self):
        for variables in (
            {"MONAD_ZKVM_OFFICIAL_PROFILE": "OFF"},
            {"MONAD_ZKVM_OFFICIAL_PROFILE": "ON", "MONAD_ZKVM_CMAKE_ARGS": "-DFOO=ON"},
            {"MONAD_ZKVM_OFFICIAL_PROFILE": "ON", "MONAD_ZKVM_GIT_COMMIT": "f" * 40},
        ):
            with self.subTest(variables=variables):
                result = self.run_helper(**variables)
                self.assertNotEqual(result.returncode, 0)
        self.script(
            self.bin / "git",
            '#!/bin/sh\ncase "$*" in\n'
            ' *rev-parse*) printf "%040d\\n" 1;;\n'
            ' *status*) echo " M changed.cpp";;\nesac\n',
        )
        result = self.run_helper(MONAD_ZKVM_OFFICIAL_PROFILE="ON")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("clean tracked worktree", result.stderr)

    def test_comparison_uses_reported_archive_not_newest(self):
        a = self.here / "target/guest-build/A/build/libmonad-zkvm-guest-zisk.a"
        b = self.here / "target/guest-build/B/build/libmonad-zkvm-guest-zisk.a"
        archive(a, b"A")
        archive(b, b"B")
        os.utime(a, (100, 100))
        os.utime(b, (200, 200))
        self.env["GUEST_ARCHIVE"] = str(a)
        result = self.run_script("test-build-archive.sh")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("OK: 1 objects identical", result.stdout)
        # The newer B is ignored, but a real mismatch still fails.
        self.env["GUEST_ARCHIVE"] = str(b)
        result = self.run_script("test-build-archive.sh")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("differs: probe.o", result.stdout)


if __name__ == "__main__":
    unittest.main()
