// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

use super::*;
use std::{fs, os::unix::fs::PermissionsExt};

// Run each build in a child process: Cargo's environment is process-global.
#[test]
fn run_archive_build() {
    if env::var_os("MONAD_TEST_ARCHIVE_CHILD").is_some() {
        println!(
            "ARCHIVE_DIR={}",
            Backend::Zisk.build_guest_archive().display()
        );
    }
}

struct Fixture(PathBuf);
impl Fixture {
    fn new() -> Self {
        let root = test_dir("monad build test");
        for dir in [
            "zkvm/guest",
            "zkvm/zisk",
            "category/core/toolchains",
            "tools/bin",
        ] {
            fs::create_dir_all(root.join(dir)).unwrap();
        }
        fs::write(root.join("zkvm/guest/CMakeLists.txt"), "# fixture\n").unwrap();
        fs::write(root.join("category/core/toolchains/riscv64-elf.cmake"), "").unwrap();
        for program in [
            "cc1",
            "cc1plus",
            "as",
            "riscv-none-elf-ar",
            "riscv-none-elf-ranlib",
        ] {
            fs::write(root.join("tools/bin").join(program), "fixture").unwrap();
        }
        for driver in ["gcc", "g++"] {
            Self::script(
                &root.join(format!("tools/bin/riscv-none-elf-{driver}")),
                r#"#!/bin/sh
case "$1" in
    -print-prog-name=*) printf '%s/%s\n' "$(dirname "$0")" "${1#-print-prog-name=}" ;;
    -E) echo '"gcc"' ;;
    *) exit 1 ;;
esac
"#,
            );
        }
        // Record the actual cmake-rs configuration without compiling the guest.
        Self::script(
            &root.join("cmake"),
            r#"#!/bin/sh
if [ "$1" = --version ]; then echo 'cmake version 3.25.0'; exit 0; fi
if [ "$1" = --build ]; then exit 0; fi
printf '%s\n' "$@" > configuration.txt
"#,
        );
        Self(root)
    }

    fn script(path: &Path, source: &str) {
        fs::write(path, source).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn build(&self, out: &str, vars: &[(&str, &str)]) -> (PathBuf, String) {
        let host = Command::new("rustc").arg("-vV").output().unwrap();
        let host = String::from_utf8(host.stdout).unwrap();
        let host = host.lines().find_map(|l| l.strip_prefix("host: ")).unwrap();
        let mut cmd = Command::new(env::current_exe().unwrap());
        cmd.args(["--exact", "build_tests::run_archive_build", "--nocapture"]);
        for name in build_env_names(Backend::Zisk.guest_triple())
            .into_iter()
            .chain(
                [
                    "MONAD_ZKVM_CMAKE_ARGS",
                    "MONAD_ZKVM_GIT_COMMIT",
                    "MONAD_ZKVM_BUILD_ID",
                    "MONAD_ZKVM_ZISK_DMA",
                    "MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES",
                    "GCC_EXEC_PREFIX",
                    "COMPILER_PATH",
                ]
                .map(String::from),
            )
        {
            cmd.env_remove(name);
        }
        cmd.env("MONAD_TEST_ARCHIVE_CHILD", "1")
            .env("CARGO_MANIFEST_DIR", self.0.join("zkvm/zisk"))
            .env("OUT_DIR", self.0.join(out))
            .env("HOST", host)
            .env("TARGET", Backend::Zisk.guest_triple())
            .env("PROFILE", "release")
            .env("OPT_LEVEL", "3")
            .env("DEBUG", "false")
            .env("NUM_JOBS", "1")
            .env("RISCV_TOOLCHAIN_DIR", self.0.join("tools"))
            .env("CMAKE", self.0.join("cmake"))
            .env("CMAKE_GENERATOR", "Unix Makefiles")
            .env("CRATE_CC_NO_DEFAULTS", "0")
            .env("CC_riscv64ima_zisk_zkvm_elf", "cc")
            .env("CXX_riscv64ima_zisk_zkvm_elf", "c++");
        for (key, value) in vars {
            cmd.env(key, value);
        }
        let result = cmd.output().unwrap();
        let stdout = String::from_utf8(result.stdout).unwrap();
        assert!(
            result.status.success(),
            "{stdout}\n{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let path = stdout
            .lines()
            .find_map(|l| l.strip_prefix("ARCHIVE_DIR="))
            .unwrap();
        (PathBuf::from(path), stdout)
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn independent_builds_keep_private_configuration_and_stamps() {
    let f = Fixture::new();
    let (a, _) = f.build("cargo-a", &[("MONAD_ZKVM_BUILD_ID", "a")]);
    let original = fs::read(a.join("configuration.txt")).unwrap();
    let (b, _) = f.build("cargo-b", &[("MONAD_ZKVM_BUILD_ID", "b")]);
    assert_ne!(a, b);
    assert_eq!(original, fs::read(a.join("configuration.txt")).unwrap());
    let (again, _) = f.build(
        "cargo-a",
        &[
            ("MONAD_ZKVM_BUILD_ID", "updated"),
            ("MONAD_ZKVM_GIT_COMMIT", "abc"),
        ],
    );
    assert_eq!(a, again);
    let cfg = fs::read_to_string(a.join("configuration.txt")).unwrap();
    assert!(cfg.contains("-DMONAD_ZKVM_BUILD_ID=updated"));
    assert!(cfg.contains("-DMONAD_ZKVM_GIT_COMMIT=abc"));
    f.build("cargo-a", &[]);
    let cfg = fs::read_to_string(a.join("configuration.txt")).unwrap();
    assert!(cfg.contains("-DMONAD_ZKVM_BUILD_ID=none"));
    assert!(cfg.lines().any(|l| l == "-DMONAD_ZKVM_GIT_COMMIT="));
}

#[test]
fn configuration_changes_select_distinct_caches_and_watch_inputs() {
    let f = Fixture::new();
    let (base, stdout) = f.build("cargo", &[]);
    for variable in ["CMAKE_PREFIX_PATH", "CMAKE_GENERATOR", "CMAKE"] {
        for name in [
            variable.to_string(),
            format!("TARGET_{variable}"),
            format!("{variable}_riscv64ima-zisk-zkvm-elf"),
            format!("{variable}_riscv64ima_zisk_zkvm_elf"),
        ] {
            assert!(
                stdout
                    .lines()
                    .any(|l| l == format!("cargo:rerun-if-env-changed={name}")),
                "{name}"
            );
        }
    }
    for pair in [
        ("CMAKE_PREFIX_PATH", "/other/boost"),
        ("CMAKE_GENERATOR_riscv64ima_zisk_zkvm_elf", "Ninja"),
        ("CFLAGS", "-DTEST_FLAG"),
        ("MONAD_ZKVM_CMAKE_ARGS", "-DTEST_OPTION=ON"),
        ("MONAD_ZKVM_ZISK_DMA", "ON"),
    ] {
        let (changed, _) = f.build("cargo", &[pair]);
        assert_ne!(base, changed, "{}", pair.0);
    }
    let (again, _) = f.build("cargo", &[]);
    assert_eq!(base, again);
    assert!(!fs::read_to_string(again.join("configuration.txt"))
        .unwrap()
        .contains("-DTEST_OPTION"));
}

#[test]
fn ambient_compilers_do_not_change_guest_flags() {
    let f = Fixture::new();
    let (base, _) = f.build("cargo", &[]);
    let before = fs::read_to_string(base.join("configuration.txt")).unwrap();
    assert!(before.contains("-march=rv64ima"));
    assert!(before.contains("-mabi=lp64"));
    let mut vars = Vec::new();
    for name in ["CC", "CXX"] {
        for variable in [
            name.to_string(),
            format!("TARGET_{name}"),
            format!("{name}_riscv64ima-zisk-zkvm-elf"),
            format!("{name}_riscv64ima_zisk_zkvm_elf"),
        ] {
            vars.push((variable, "/nonexistent/compiler"));
        }
    }
    let refs: Vec<_> = vars.iter().map(|(k, v)| (k.as_str(), *v)).collect();
    let (after, _) = f.build("cargo", &refs);
    assert_eq!(base, after);
    assert_eq!(
        before,
        fs::read_to_string(after.join("configuration.txt")).unwrap()
    );
}
