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

//! Build-script helpers for the ZisK and SP1 RISC-V guests.
//! Both build `zkvm/guest/CMakeLists.txt`; ZisK links the archive through
//! rustc, while SP1 links a standalone ELF against the SDK's `libzkevm.a`.

use std::{
    env,
    path::{Path, PathBuf},
    process::Command,
};

mod toolchain;

#[derive(Clone, Copy, Debug)]
pub enum Backend {
    Zisk,
    Sp1,
}

impl Backend {
    fn name(self) -> &'static str {
        match self {
            Self::Zisk => "zisk",
            Self::Sp1 => "sp1",
        }
    }

    fn guest_target(self) -> &'static str {
        match self {
            Self::Zisk => "monad-zkvm-guest-zisk",
            Self::Sp1  => "monad-zkvm-guest-sp1",
       }
    }

    fn guest_triple(self) -> &'static str {
        match self {
            Self::Zisk => "riscv64ima-zisk-zkvm-elf",
            Self::Sp1 => "riscv64im-succinct-zkvm-elf",
        }
    }

    /// Cross-compile the guest archive and return its directory.
    fn build_guest_archive(self) -> PathBuf {
        let manifest = manifest_dir();
        let repo_root = locate_repo_root(&manifest);
        let zkvm_dir = repo_root.join("zkvm");
        let guest_dir = zkvm_dir.join("guest");
        let toolchain = repo_root.join("category/core/toolchains/riscv64-elf.cmake");

        emit_rerun_directives(&repo_root);

        let mut cfg = cmake::Config::new(&guest_dir);
        // Reuse objects across commits, but not after a compiler rebuild.
        // Include GCC's frontends: rebuilding them need not change the driver.
        // Store them under zkvm/<backend>/target/guest-build.
        let toolchain_dir = riscv_toolchain_dir();
        let mut key = format!(
            "{}-{}",
            self.name(),
            toolchain::fingerprint(&riscv_gcc(&toolchain_dir))
        );
        if env::var_os("MONAD_ZKVM_OFFICIAL_PROFILE").is_some() {
            key.push_str("-official");
        }
        cfg.out_dir(
            repo_root
                .join("zkvm")
                .join(self.name())
                .join("target/guest-build")
                .join(&key),
        );
        // SP1's caller targets the host. Set the guest triple explicitly so
        // cmake-rs selects RISC-V flags instead of host flags such as -m64.
        // The guest CMakeLists.txt supplies the remaining bare-metal flags.
        cfg.target(self.guest_triple())
            .define("MONAD_ZKVM_GUEST_TARGET", self.name())
            .define("CMAKE_TOOLCHAIN_FILE", &toolchain)
            .define("RISCV_TOOLCHAIN_DIR", &toolchain_dir)
            .profile("Release")
            .build_target(&self.guest_target());

        // Allow discovery of the host's header-only Boost.Outcome package.
        let prefix_path = env::var("CMAKE_PREFIX_PATH").unwrap_or_else(|_| "/usr".to_string());
        cfg.define("CMAKE_PREFIX_PATH", &prefix_path);

        // Keep official-profile settings explicit instead of forwarding
        // arbitrary CMake definitions.
        match env::var("MONAD_ZKVM_OFFICIAL_PROFILE") {
            Ok(profile) => {
                assert_eq!(
                    profile, "ON",
                    "MONAD_ZKVM_OFFICIAL_PROFILE must be ON or unset"
                );
                assert!(
                    env::var("MONAD_ZKVM_CMAKE_DEFINES").is_err(),
                    "MONAD_ZKVM_CMAKE_DEFINES cannot be combined with the official profile"
                );
                cfg.define("MONAD_ZKVM_OFFICIAL_PROFILE", "ON")
                    .define("MONAD_ZKVM_GIT_COMMIT", official_build_commit(&repo_root));
            }
            // Outside the official profile, keep the caller's commit label.
            Err(_) => {
                if let Ok(commit) = env::var("MONAD_ZKVM_GIT_COMMIT") {
                    cfg.define("MONAD_ZKVM_GIT_COMMIT", commit);
                }
                // Development-only overrides: "NAME=VALUE;FLAG" (FLAG means ON).
                // Cargo does not track this variable; rebuild cleanly after
                // changing or removing it.
                if let Ok(defs) = env::var("MONAD_ZKVM_CMAKE_DEFINES") {
                    for kv in defs.split(';').filter(|s| !s.trim().is_empty()) {
                        let (k, v) = kv.split_once('=').unwrap_or((kv, "ON"));
                        cfg.define(k.trim(), v.trim());
                    }
                }
            }
        }

        cfg.build().join("build")
    }

    /// Build the guest archive and emit Cargo link directives.
    /// Used by ZisK, where `ziskos` supplies `_start`.
    pub fn build_guest_lib(self) {
        let build_dir = self.build_guest_archive();

        if let Self::Zisk = self {
            let align_ld = manifest_dir().join("align.ld");
            println!("cargo:rerun-if-changed={}", align_ld.display());
            println!("cargo:rustc-link-arg=-T{}", align_ld.display());
        }
        println!("cargo:rustc-link-arg=--gc-sections");
        println!("cargo:rustc-link-search=native={}", build_dir.display());
        println!("cargo:rustc-link-lib=static={}", self.guest_target());
    }

    /// Build the SP1 guest ELF from `program/main.c`, the guest archive, and
    /// the SDK's `libzkevm.a`, which supplies the runtime and accelerators.
    /// The SDK library, headers, and linker script come from one checkout.
    #[cfg(feature = "sp1")]
    pub fn build_guest_elf(self) -> PathBuf {
        assert!(matches!(self, Self::Sp1), "build_guest_elf is SP1-only");

        let repo_root = locate_repo_root(&manifest_dir());
        let gcc = riscv_gcc(&riscv_toolchain_dir());

        let build_dir = self.build_guest_archive();
        let archive = build_dir.join(format!("lib{}.a", self.guest_target()));

        let zkevm = sp1_zkevm_dir();
        let libzkevm = sp1_build::build_program_staticlib(
            zkevm
                .join("libzkevm-cabi")
                .to_str()
                .expect("cabi path is utf-8"),
        );
        let include = zkevm.join("include");

        let main_c = repo_root.join("zkvm/sp1/program/main.c");
        let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR unset"));
        let main_o = out_dir.join("main.o");
        let elf = out_dir.join("monad-zkvm-guest-sp1.elf");

        // The SDK's zkvm.ld plus our overlay adding the C++ guest's RELRO
        // sections (see relro.ld).
        let zkvm_ld = zkevm.join("zkvm.ld");
        let relro_ld = repo_root.join("zkvm/sp1/program/relro.ld");

        println!("cargo:rerun-if-changed={}", main_c.display());
        println!("cargo:rerun-if-changed={}", relro_ld.display());

        let status = Command::new(&gcc)
            .args([
                "-march=rv64im",
                "-mabi=lp64",
                "-mcmodel=medany",
                "-nostdlib",
                "-ffreestanding",
                "-fno-builtin",
                "-O2",
                "-Wall",
                "-Wextra",
                "-c",
            ])
            .arg(format!("-I{}", include.display()))
            .arg("-o")
            .arg(&main_o)
            .arg(&main_c)
            .status()
            .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", gcc.display()));
        assert!(
            status.success(),
            "gcc failed compiling {}",
            main_c.display()
        );

        let lld = sp1_build::find_lld().expect(
            "ld.lld not found on PATH and no SP1 toolchain has a bundled copy. \
             Install lld (`apt install lld`) or run `sp1up`.",
        );
        // Unreachable archive sections reference symbols this guest doesn't
        // provide. Discard them before resolving references.
        let status = Command::new(&lld)
            .args(["-nostdlib", "-static", "--gc-sections"])
            .arg(format!("-T{}", zkvm_ld.display()))
            .arg(format!("-T{}", relro_ld.display()))
            .arg("-o")
            .arg(&elf)
            .arg(&main_o)
            .arg(&archive)
            .arg(&libzkevm)
            .status()
            .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", lld.display()));
        assert!(status.success(), "ld.lld failed linking {}", elf.display());

        elf
    }
}

/// Locate the SDK sources in Cargo's `sp1-build` git checkout.
#[cfg(feature = "sp1")]
fn sp1_zkevm_dir() -> PathBuf {
    let meta = cargo_metadata::MetadataCommand::new()
        .exec()
        .expect("cargo metadata failed while locating the sp1-build checkout");
    // Match the git-sourced sp1-build (our dep), not the crates.io `sp1-build`
    // the prover pulls in — only the git checkout carries the zkevm/ tree.
    let pkg = meta
        .packages
        .iter()
        .find(|p| {
            p.name == "sp1-build"
                && p.source
                    .as_ref()
                    .map_or(false, |s| s.repr.contains("succinctlabs/sp1"))
        })
        .expect("git-sourced sp1-build not found in cargo metadata");
    // <checkout>/crates/build/Cargo.toml -> <checkout> -> <checkout>/zkevm
    let manifest = pkg.manifest_path.clone().into_std_path_buf();
    let checkout = manifest
        .ancestors()
        .nth(3)
        .expect("unexpected sp1-build manifest path layout");
    let zkevm = checkout.join("zkevm");
    assert!(
        zkevm.join("libzkevm-cabi/Cargo.toml").exists(),
        "SP1 zkevm source not found at {} — sp1-build git checkout incomplete?",
        zkevm.display()
    );
    zkevm
}

/// Use Git HEAD, rejecting a mismatched supplied SHA or reported tracked changes.
/// Without a usable HEAD, require MONAD_ZKVM_GIT_COMMIT (e.g. source archives).
fn official_build_commit(repo_root: &Path) -> String {
    let git = |args: &[&str]| -> Option<String> {
        let out = Command::new("git")
            .arg("-C")
            .arg(repo_root)
            .args(args)
            .output()
            .ok()?;
        out.status
            .success()
            .then(|| String::from_utf8_lossy(&out.stdout).trim().to_string())
    };
    let supplied = env::var("MONAD_ZKVM_GIT_COMMIT").ok();
    let head = match git(&["rev-parse", "HEAD"]) {
        Some(h) if h.len() == 40 => h,
        _ => {
            return supplied.expect(
                "official ZisK profile: no git in the build tree, so \
                 MONAD_ZKVM_GIT_COMMIT must supply the commit",
            );
        }
    };
    // Check tracked changes; untracked files are excluded here.
    if let Some(dirty) = git(&["status", "--porcelain", "--untracked-files=no"]) {
        assert!(
            dirty.is_empty(),
            "official ZisK profile: the worktree is dirty, so no commit \
             describes what would be built:\n{dirty}"
        );
    }
    if let Some(supplied) = supplied {
        assert_eq!(
            supplied, head,
            "MONAD_ZKVM_GIT_COMMIT does not match the tree being built"
        );
    }
    head
}

fn manifest_dir() -> PathBuf {
    PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR unset"))
}

fn locate_repo_root(manifest: &Path) -> PathBuf {
    manifest
        .ancestors()
        .find(|p| p.join("zkvm/guest/CMakeLists.txt").exists())
        .expect("failed to locate monad repo root from build.rs CARGO_MANIFEST_DIR")
        .to_path_buf()
}

fn emit_rerun_directives(repo_root: &Path) {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=RISCV_TOOLCHAIN_DIR");
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_OFFICIAL_PROFILE");
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_GIT_COMMIT");
    // Watch Git metadata to refresh the build stamp when only the commit changes. Git names the
    // paths: in a linked worktree `.git` is a file, HEAD lives in the worktree's own git
    // directory and refs in the common one, and a branch's ref may be packed.
    let git_path = |args: &[&str]| -> Option<PathBuf> {
        let out = Command::new("git")
            .arg("-C")
            .arg(repo_root)
            .args(args)
            .output()
            .ok()?;
        out.status.success().then(|| {
            let p = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
            if p.is_absolute() {
                p
            } else {
                repo_root.join(p)
            }
        })
    };
    let head = git_path(&["rev-parse", "--git-path", "HEAD"]);
    let common = git_path(&["rev-parse", "--git-common-dir"]);
    let refs = common
        .iter()
        .flat_map(|c| [c.join("refs"), c.join("packed-refs")]);
    for p in head.into_iter().chain(refs) {
        if p.exists() {
            println!("cargo:rerun-if-changed={}", p.display());
        }
    }
    // Everything the guest cmake build reads. Emitting any rerun-if-changed
    // disables Cargo's rerun-on-any-change default, so an input missing here
    // leaves a stale guest marked fresh. Cargo scans each directory
    // recursively, including added files. Keep in sync with the include
    // paths and vendored sources in zkvm/guest/CMakeLists.txt and
    // cmake/zkvm.cmake.
    for dir in [
        // The guest build itself and the shadow tree searched ahead of the
        // host sources (zkvm/{boost,quill,immer} are shadow headers).
        "zkvm/guest",
        "zkvm/core",
        "zkvm/category",
        "zkvm/boost",
        "zkvm/quill",
        "zkvm/test",
        "category",
        "cmake",
        // Vendored sources on the guest include path. third_party/ as a whole
        // is not watched: it holds large test-suite submodules the guest
        // never reads.
        "third_party/blst",
        "third_party/cthash",
        "third_party/ethash_vendor",
        "third_party/evmc",
        "third_party/immer",
        "third_party/komihash",
        "third_party/nlohmann_json",
        "third_party/silkpre_vendor",
        "third_party/unordered_dense",
        "third_party/zkevm-standards",
    ] {
        println!("cargo:rerun-if-changed={}", repo_root.join(dir).display());
    }
}

fn riscv_toolchain_dir() -> String {
    let dir = env::var("RISCV_TOOLCHAIN_DIR").unwrap_or_default();
    assert!(
        !dir.is_empty(),
        "RISCV_TOOLCHAIN_DIR is not set. Create zkvm/.cargo/config.toml with \
         `[env] RISCV_TOOLCHAIN_DIR = \"/path/to/riscv_gcc\"` (see zkvm/README.md).",
    );
    dir
}

// Match the compiler prefixes accepted by riscv64-elf.cmake.
fn riscv_gcc(toolchain_dir: &str) -> PathBuf {
    let bin = Path::new(toolchain_dir).join("bin");
    for prefix in ["riscv64-none-elf-", "riscv64-unknown-elf-", "riscv-none-elf-"] {
        let gcc = bin.join(format!("{prefix}gcc"));
        if gcc.exists() {
            return gcc;
        }
    }
    panic!(
        "no RISC-V gcc (riscv64-none-elf-gcc, riscv64-unknown-elf-gcc or riscv-none-elf-gcc) found in {}",
        bin.display()
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{fs, time::SystemTime};

    #[test]
    fn accepts_cmake_compiler_prefixes_in_order() {
        let dir = env::temp_dir().join(format!(
            "monad-gcc-prefixes-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let bin = dir.join("bin");
        fs::create_dir_all(&bin).unwrap();
        let prefixes = ["riscv64-none-elf-", "riscv64-unknown-elf-", "riscv-none-elf-"];
        for prefix in prefixes {
            fs::write(bin.join(format!("{prefix}gcc")), "").unwrap();
        }
        for prefix in prefixes {
            let expected = bin.join(format!("{prefix}gcc"));
            assert_eq!(riscv_gcc(dir.to_str().unwrap()), expected);
            fs::remove_file(expected).unwrap();
        }
        fs::remove_dir_all(dir).unwrap();
    }
}
