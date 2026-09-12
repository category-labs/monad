"""Run with python3 -m unittest discover -s zkvm/zisk -p 'test_audit_*.py'."""

from __future__ import annotations

import importlib.util
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "audit_official_build", Path(__file__).with_name("audit-official-build.py")
)
audit = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(audit)


def valid_flags() -> str:
    return " ".join(
        (
            *audit.REQUIRED_FLAGS,
            f"-march={audit.EXPECTED_MARCH}",
            f"-mtune={audit.EXPECTED_MTUNE}",
        )
    )


class FlagTests(unittest.TestCase):
    def test_current_flags_and_quoted_paths(self):
        audit.check_flags(
            valid_flags() + ' -include "/path with spaces/nodelete.hpp"', "test"
        )

    def test_both_parameter_spellings(self):
        audit.check_flags(valid_flags().replace("--param=", "--param "), "test")

    def test_each_required_flag_is_required(self):
        for flag in audit.REQUIRED_FLAGS:
            with self.subTest(flag=flag), self.assertRaises(SystemExit):
                audit.check_flags(valid_flags().replace(flag, ""), "test")

    def test_later_parameter_wins_with_either_spelling(self):
        for flag in audit.REQUIRED_FLAGS:
            if not flag.startswith("--param="):
                continue
            wrong = flag.rsplit("=", 1)[0] + "=9999"
            for spelling in [wrong, wrong.replace("--param=", "--param ")]:
                with self.subTest(flag=spelling):
                    with self.assertRaises(SystemExit):
                        audit.check_flags(valid_flags() + " " + spelling, "test")
                    audit.check_flags(spelling + " " + valid_flags(), "test")

    def test_later_codegen_overrides_are_rejected(self):
        for override in [
            "-O2", "-Os", "-march=rv64ima", "-mtune=size", "-mabi=ilp32",
            "-fpic", "-fPIC", "-fno-unroll-loops",
            "-fno-inline-functions", "-mno-zisk-dma",
        ]:
            with self.subTest(override=override):
                with self.assertRaises(SystemExit):
                    audit.check_flags(valid_flags() + " " + override, "test")
                audit.check_flags(override + " " + valid_flags(), "test")

    def test_flags_make_uses_only_cxx_flags(self):
        audit.check_flags(
            "# -O0\nCXX_FLAGS = " + valid_flags() + "\nC_FLAGS = -O0\n", "test"
        )
        with self.assertRaises(SystemExit):
            audit.check_flags("C_FLAGS = " + valid_flags(), "test")
        with self.assertRaises(SystemExit):
            audit.check_flags(
                "C_FLAGS = " + valid_flags() + "\nCXX_FLAGS = -O0\n", "test"
            )

    def test_malformed_parameters_and_quotes_fail(self):
        for tail in ["--param", "--param name", "--param==1", "--param=name=", '"']:
            with self.subTest(tail=tail), self.assertRaises(SystemExit):
                audit.check_flags(valid_flags() + " " + tail, "test")


class ProfileTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve()
        self.repo = self.root / "repo"
        self.build_root = self.root / "target/guest-build"
        self.build_dir = self.build_root / "zisk-toolchain-official/build"
        self.commit = "a" * 40
        self.compiler = self.root / "riscv64-unknown-elf-g++"
        self.compiler.write_bytes(b"test compiler")
        self.nm = self.root / "riscv64-unknown-elf-nm"
        self.readelf = self.root / "riscv64-unknown-elf-readelf"
        self.nm.touch()
        self.readelf.touch()
        self.cargo = self.root / "cargo-zisk"
        self.elf = self.root / "guest.elf"
        self.manifest = self.root / "manifest.json"
        guest = self.repo / "zkvm/guest"
        core = self.repo / "zkvm/core"
        zisk = self.repo / "zkvm/zisk"
        for directory in [guest, core, zisk]:
            directory.mkdir(parents=True)
        overloads = [
            "operator delete(void *)", "operator delete[](void *)",
            "operator delete(void *, std::size_t)",
            "operator delete[](void *, std::size_t)",
        ]
        (guest / "nodelete.hpp").write_text("\n".join(
            f"[[gnu::const]] void {overload} noexcept;" for overload in overloads
        ))
        (core / "libstdcxx.cpp").write_text("\n".join(
            f"void {overload} noexcept {{}}" for overload in overloads
        ))
        (core / "libc.cpp").write_text("void free(void *ptr)\n{\n    (void)ptr;\n}\n")
        (zisk / "Cargo.lock").write_text(
            f'[[package]]\nname = "ziskos"\nversion = "{audit.RUNTIME_VERSION}"\n'
            f'source = "{audit.RUNTIME_SOURCE}"\n'
        )
        self.flags = valid_flags() + f' -include "{guest}/nodelete.hpp"'
        self.profile = {
            "schema": 2, "target": "zisk", "commit": self.commit,
            "runtime_version": audit.RUNTIME_VERSION,
            "runtime_revision": audit.RUNTIME_REVISION,
            "features_csv": "baseline,zisk-dma", "build_signature": "b" * 64,
            "compiler": str(self.compiler), "compiler_id": "GNU",
            "compiler_version": "15.2.0",
            "compiler_sha256": audit.sha256(self.compiler),
            "cxx_flags": self.flags, "cxx_flags_release": "",
        }
        marker = (
            f"{audit.PROFILE};runtime=ziskos-{audit.RUNTIME_VERSION};"
            f"features=baseline,zisk-dma;commit={self.commit};signature={'b' * 64}"
        )
        self.elf.write_bytes(marker.encode())
        self.profile_path = self.write_profile(self.build_dir, self.profile)

    def write_profile(self, directory, profile):
        directory.mkdir(parents=True, exist_ok=True)
        profile_path = directory / "monad-zkvm-official-profile.json"
        profile_path.write_text(json.dumps(profile))
        (directory / "CMakeCache.txt").write_text(
            "MONAD_ZKVM_OFFICIAL_PROFILE:BOOL=ON\nMONAD_ZKVM_GUEST_TARGET:STRING=zisk\n"
        )
        flags_dir = directory / "CMakeFiles/monad-zkvm-guest-zisk.dir"
        flags_dir.mkdir(parents=True, exist_ok=True)
        (flags_dir / "flags.make").write_text("CXX_FLAGS = " + self.flags + "\n")
        return profile_path

    def run_tool(self, *args):
        if args[0] == "git" and "status" in args:
            return ""
        if args[0] == "git" and "rev-parse" in args:
            return self.commit
        if args == (str(self.cargo), "--version"):
            return f"cargo-zisk {audit.RUNTIME_VERSION} test"
        if args == (str(self.readelf), "-A", str(self.elf)):
            return "rv64ima_zicsr_zbb_zbs_zbkb"
        raise AssertionError(args)

    def run_audit(self):
        argv = [
            "audit", "--elf", str(self.elf), "--build-root", str(self.build_root),
            "--repo", str(self.repo), "--cargo-zisk", str(self.cargo),
            "--manifest", str(self.manifest),
        ]
        with patch.object(sys, "argv", argv), \
                patch.object(audit, "run", side_effect=self.run_tool), \
                patch.object(audit.subprocess, "check_output", return_value=""), \
                redirect_stdout(io.StringIO()):
            self.assertEqual(audit.main(), 0)

    def test_new_layout_produces_manifest(self):
        self.run_audit()
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(manifest["commit"], self.commit)
        self.assertEqual(
            manifest["evidence"]["cmake_profile_sha256"],
            audit.sha256(self.profile_path),
        )

    def test_newer_profile_with_different_identity_is_ignored(self):
        stale = dict(self.profile, build_signature="c" * 64)
        path = self.write_profile(self.build_root / "stale/build", stale)
        later = self.profile_path.stat().st_mtime_ns + 10_000_000_000
        os.utime(path, ns=(later, later))
        self.run_audit()
        manifest = json.loads(self.manifest.read_text())
        self.assertEqual(
            manifest["evidence"]["cmake_profile_sha256"],
            audit.sha256(self.profile_path),
        )

    def test_wrong_commit_or_signature_cannot_supply_profile(self):
        for changes in [{"commit": "c" * 40}, {"build_signature": "c" * 64}]:
            with self.subTest(changes=changes):
                self.profile_path.write_text(json.dumps(dict(self.profile, **changes)))
                with self.assertRaisesRegex(SystemExit, "no generated CMake profile"):
                    self.run_audit()
                self.assertFalse(self.manifest.exists())

    def test_old_cargo_layout_is_not_selected(self):
        self.profile_path.unlink()
        self.write_profile(self.build_root / "old/out/build", self.profile)
        with self.assertRaisesRegex(SystemExit, "no generated CMake profile"):
            self.run_audit()

    def test_generated_flags_are_checked(self):
        profile = dict(self.profile, cxx_flags=self.flags + " -mtune=size")
        self.profile_path.write_text(json.dumps(profile))
        with self.assertRaisesRegex(SystemExit, r"generated C\+\+ profile has -mtune"):
            self.run_audit()

    def test_compile_command_flags_are_checked(self):
        flags = self.build_dir / "CMakeFiles/monad-zkvm-guest-zisk.dir/flags.make"
        flags.write_text("CXX_FLAGS = " + self.flags + " -mno-zisk-dma\n")
        with self.assertRaisesRegex(SystemExit, "guest compile command has -mzisk-dma"):
            self.run_audit()


if __name__ == "__main__":
    unittest.main()
