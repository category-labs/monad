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

"""Allocator assumptions and linked-code checks for the reference build."""

import importlib.util
from pathlib import Path
import shutil
import os
import subprocess
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("check_zisk", Path(__file__).with_name("check-zisk.py"))
check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check)
REPO = Path(__file__).resolve().parent.parent


class ZiskChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        for name in ("zkvm/guest/nodelete.hpp", "zkvm/core/libstdcxx.cpp", "zkvm/core/libc.cpp"):
            dest = self.repo / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / name, dest)

    def test_current_allocator(self):
        check.check_allocator(self.repo)

    def test_delete_body_is_checked_even_when_absent_from_elf(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        p.write_text(p.read_text().replace("noexcept {}", "noexcept { abort(); }", 1))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_new_overload_cannot_hide_a_body(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        with p.open("a") as f:
            f.write("void operator delete(void *p, std::align_val_t) noexcept { abort(); }\n")
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_missing_definition_is_rejected(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        p.write_text(p.read_text().replace("void operator delete(void *) noexcept {}", ""))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_comment_cannot_supply_a_definition(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        p.write_text(p.read_text().replace("void operator delete(void *) noexcept {}", "// void operator delete(void *) noexcept {}"))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_free_body_is_checked(self):
        p = self.repo / "zkvm/core/libc.cpp"
        p.write_text(p.read_text().replace("(void)ptr;", "(void)ptr; abort();"))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_ret_encoding(self):
        check.check_return("80000000: 00008067 ret\n")
        for code in ("80000000: 00100073 ebreak\n", "", "80000000: 00008067 ret\n80000004: 00000013 nop\n"):
            with self.subTest(code=code), self.assertRaises(ValueError):
                check.check_return(code)

    def test_elf_checks_identity_isa_and_surviving_functions(self):
        elf = self.repo / "guest"
        commit = "a" * 40
        elf.write_bytes(b"monad-zkvm;commit=" + commit.encode() + b";build=none\0")
        with self.assertRaises(ValueError):
            check.check_elf(elf, commit, "riscv-", "another-build")
        attrs = 'Tag_RISCV_arch: "rv64i2p1_m2p0_a2p1_zba1p0_zbb1p0_zbs1p0_zbkb1p0"'
        nm = "80000000 00000004 T free\n"
        with patch.object(check.subprocess, "check_output", side_effect=[attrs, nm, "80000000: 00008067 ret\n"]):
            check.check_elf(elf, commit, "riscv-")
        with self.assertRaises(ValueError):
            check.check_elf(elf, "b" * 40, "riscv-")
        with patch.object(check.subprocess, "check_output", return_value=attrs.replace("_zba1p0", "")), self.assertRaises(ValueError):
            check.check_elf(elf, commit, "riscv-")
        with patch.object(check.subprocess, "check_output", side_effect=[attrs, nm, "80000000: 00100073 ebreak\n"]), self.assertRaises(ValueError):
            check.check_elf(elf, commit, "riscv-")


class RustWrapperChecks(unittest.TestCase):
    def test_normalizes_root_metadata_and_build_paths(self):
        wrapper = REPO / "nix/zisk-rustc-wrapper.sh"
        def run(crate):
            args = ["sh", str(wrapper), sys.executable, "-c",
                    "import json,sys; print(json.dumps(sys.argv[1:]))",
                    "--crate-name", crate, "-C", "metadata=random"]
            env = dict(os.environ, ZISK_ROOT_CRATE="monad_zkvm_zisk", NIX_BUILD_TOP="/tmp/random-build")
            return json.loads(subprocess.check_output(args, env=env, text=True))
        root = run("monad_zkvm_zisk")
        self.assertIn("metadata=monad_zkvm_zisk", root)
        self.assertIn("--remap-path-prefix=/tmp/random-build=/build", root)
        self.assertIn("metadata=random", run("dependency"))


if __name__ == "__main__":
    unittest.main()
