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
};
#[cfg(feature = "sp1")]
use std::process::Command;

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
        // SP1's caller targets the host. Set the guest triple explicitly so
        // cmake-rs selects RISC-V flags instead of host flags such as -m64.
        // The guest CMakeLists.txt supplies the remaining bare-metal flags.
        cfg.target(self.guest_triple())
            .define("MONAD_ZKVM_GUEST_TARGET", self.name())
            .define("CMAKE_TOOLCHAIN_FILE", &toolchain)
            .define("RISCV_TOOLCHAIN_DIR", riscv_toolchain_dir())
            .profile("Release")
            .build_target(&self.guest_target());

        // Allow discovery of the host's header-only Boost.Outcome package.
        let prefix_path = env::var("CMAKE_PREFIX_PATH").unwrap_or_else(|_| "/usr".to_string());
        cfg.define("CMAKE_PREFIX_PATH", &prefix_path);

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
        self.link_guest_elf("zkvm/sp1/program/main.c", "monad-zkvm-guest-sp1.elf")
    }
    
    /// SP1 guest ELF for the precompile golden-vector test entry. Same link as
    /// [`Self::build_guest_elf`], but with the precompile-test `main.c` (which
    /// calls `monad_zkvm_run_precompile_tests` instead of the witness entry).
    #[cfg(feature = "sp1")]
    pub fn build_precompile_test_elf(self) -> PathBuf {
        self.link_guest_elf(
            "zkvm/test/precompile_tests/sp1_main.c",
            "monad-zkvm-precompile-test-sp1.elf",
        )
    }

    /// Compile `main_rel` (a C entry relative to the repo root) and link it with
    /// the shared guest archive + `libzkevm.a` into `elf_name`. The archive and
    /// `libzkevm.a` builds are incremental/cached, so linking a second entry is
    /// cheap.
    #[cfg(feature = "sp1")]
    fn link_guest_elf(self, main_rel: &str, elf_name: &str) -> PathBuf {
        assert!(matches!(self, Self::Sp1), "link_guest_elf is SP1-only");

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

        let main_c = repo_root.join(main_rel);
        let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR unset"));
        let main_o = out_dir.join(format!("{elf_name}.main.o"));
        let elf = out_dir.join(elf_name);

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
#[cfg(feature = "sp1")]
fn riscv_gcc(toolchain_dir: &str) -> PathBuf {
    let bin = Path::new(toolchain_dir).join("bin");
    for prefix in ["riscv64-none-elf-", "riscv64-unknown-elf-"] {
        let gcc = bin.join(format!("{prefix}gcc"));
        if gcc.exists() {
            return gcc;
        }
    }
    panic!(
        "no riscv64 gcc (riscv64-none-elf-gcc or riscv64-unknown-elf-gcc) found in {}",
        bin.display()
    );
}
