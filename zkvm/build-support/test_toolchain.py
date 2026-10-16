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

"""Toolchain cache invalidation shared by Cargo and standalone builds."""

from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from toolchain import fingerprint


class ToolchainTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="monad-toolchain-")
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve()
        self.bin = self.root / "bin"
        self.bin.mkdir()
        for driver in ("gcc", "g++"):
            path = self.bin / ("riscv-none-elf-" + driver)
            path.write_text(
                '#!/bin/sh\nprintf "%s/../%s\\n" "$(dirname "$0")" "${1#-print-prog-name=}"\n'
            )
            path.chmod(0o755)
        self.components = (
            "cc1", "cc1plus", "as",
            "bin/riscv-none-elf-ar", "bin/riscv-none-elf-ranlib",
        )
        for name in self.components:
            (self.root / name).write_text("version 1")
        self.gcc = self.bin / "riscv-none-elf-gcc"

    def test_compiler_replacement_invalidates_cache(self):
        original, _ = fingerprint(self.gcc)
        self.assertEqual(fingerprint(self.gcc)[0], original)
        # Every component is hashed, even if its path and size are unchanged.
        for name in self.components:
            with self.subTest(name=name):
                path = self.root / name
                path.write_text("version 2")
                self.assertNotEqual(fingerprint(self.gcc)[0], original)
                path.write_text("version 1")
                self.assertEqual(fingerprint(self.gcc)[0], original)
        cxx = self.bin / "riscv-none-elf-g++"
        cxx.write_text(cxx.read_text() + "# rebuilt driver\n")
        self.assertNotEqual(fingerprint(self.gcc)[0], original)

    def test_symlink_content_and_target_are_tracked(self):
        target = self.root / "cc1plus-real"
        target.write_text("version 1")
        link = self.root / "cc1plus"
        link.unlink()
        link.symlink_to(target)
        original, paths = fingerprint(self.gcc)
        self.assertIn(self.bin / ".." / link.name, paths)
        self.assertIn(target, paths)
        target.write_text("version 2")
        self.assertNotEqual(fingerprint(self.gcc)[0], original)
        target.write_text("version 1")
        replacement = self.root / "cc1plus-rebuilt"
        replacement.write_text("version 1")
        link.unlink()
        link.symlink_to(replacement)
        self.assertNotEqual(fingerprint(self.gcc)[0], original)
        self.assertIn(replacement, fingerprint(self.gcc)[1])

    def test_cli_reports_digest_and_watched_paths(self):
        script = Path(__file__).with_name("toolchain.py")
        digest, paths = fingerprint(self.gcc)
        self.assertIn(self.bin, paths)
        for name in self.components:
            self.assertIn((self.root / name).resolve(), paths)
        result = subprocess.check_output([sys.executable, str(script), str(self.gcc)], text=True)
        self.assertEqual(result, digest + "\n")
        result = subprocess.check_output(
            [sys.executable, str(script), str(self.gcc), "--watch-paths"], text=True
        )
        self.assertEqual(result.splitlines(), [digest, *map(str, paths)])

    def test_missing_component_fails(self):
        (self.root / "cc1plus").unlink()
        with self.assertRaises(FileNotFoundError):
            fingerprint(self.gcc)

    def test_cargo_reruns_after_frontend_or_helper_changes(self):
        # Exercise Cargo's actual freshness checks with a tiny host crate.
        support = Path(__file__).resolve().parent
        crate = self.root / "cargo-probe"
        (crate / "src").mkdir(parents=True)
        (crate / "Cargo.toml").write_text(
            '[package]\nname = "toolchain-probe"\nversion = "0.1.0"\n'
            'edition = "2021"\n[workspace]\n'
        )
        (crate / "src/lib.rs").write_text("")
        shutil.copy2(support / "toolchain.py", crate / "toolchain.py")
        (crate / "build.rs").write_text(
            f'#[path = r"{support / "src/toolchain.rs"}"] mod toolchain;\n'
            'fn main() {\n'
            f'    let hash = toolchain::fingerprint(std::path::Path::new(r"{self.gcc}"));\n'
            '    std::fs::write("digest.txt", hash).unwrap();\n'
            '}\n'
        )

        def build():
            result = subprocess.run(
                ["cargo", "build", "--offline", "--quiet"], cwd=crate,
                capture_output=True, text=True,
            )
            self.assertEqual(result.returncode, 0, result.stderr)
            report = crate / "digest.txt"
            return report.read_text(), report.stat().st_mtime_ns

        original = build()
        self.assertEqual(build(), original)
        (self.root / "cc1plus").write_text("version 2")
        changed = build()
        self.assertNotEqual(changed[0], original[0])
        self.assertEqual(changed[0], fingerprint(self.gcc)[0])
        with (crate / "toolchain.py").open("a") as helper:
            helper.write("\n# helper changed\n")
        rebuilt = build()
        self.assertEqual(rebuilt[0], changed[0])
        self.assertNotEqual(rebuilt[1], changed[1])


if __name__ == "__main__":
    unittest.main()
