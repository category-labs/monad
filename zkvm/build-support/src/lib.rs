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

//! Build-script helpers for the RISC-V zkVM guests. Each backend builds
//! `zkvm/guest/CMakeLists.txt` into a static archive and links it through
//! rustc.

use std::{
    env,
    path::{Path, PathBuf},
};

#[derive(Clone, Copy, Debug)]
pub enum Backend {
    Zisk,
}

impl Backend {
    fn name(self) -> &'static str {
        match self {
            Self::Zisk => "zisk",
        }
    }

    fn guest_target(self) -> &'static str {
        match self {
            Self::Zisk => "monad-zkvm-guest-zisk",
        }
    }

    fn guest_triple(self) -> &'static str {
        match self {
            Self::Zisk => "riscv64ima-zisk-zkvm-elf",
        }
    }

    /// Cross-compile the guest archive and return its directory.
    fn build_guest_archive(self) -> PathBuf {
        let manifest = manifest_dir();
        let repo_root = locate_repo_root(&manifest);
        emit_rerun_directives(&repo_root);

        let guest_dir = repo_root.join("zkvm/guest");
        let toolchain = repo_root.join("category/core/toolchains/riscv64-elf.cmake");
        let toolchain_dir = riscv_toolchain_dir();
        // Allow discovery of the host's header-only Boost.Outcome package.
        let prefix_path = env::var("CMAKE_PREFIX_PATH").unwrap_or_else(|_| "/usr".to_string());

        let mut defines = vec![
            (
                "MONAD_ZKVM_GUEST_TARGET".to_string(),
                self.name().to_string(),
            ),
            (
                "CMAKE_TOOLCHAIN_FILE".into(),
                toolchain.display().to_string(),
            ),
            ("RISCV_TOOLCHAIN_DIR".into(), toolchain_dir.clone()),
            ("CMAKE_PREFIX_PATH".into(), prefix_path),
        ];
        match self {
            Self::Zisk => {
                for option in ZISK_OPTIONS {
                    println!("cargo:rerun-if-env-changed={option}");
                    defines.push((
                        option.into(),
                        env::var(option).unwrap_or_else(|_| "OFF".into()),
                    ));
                }
            }
        }

        // Isolate configurations in Cargo's OUT_DIR; the commit stamp stays
        // out of the key so objects can be reused across commits. Immutable Nix
        // toolchain paths identify the compilers without hashing their contents.
        let mut config = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&defines, &mut config);
        // cmake-rs reads these without a rerun directive; a generator change
        // cannot reuse an existing build directory.
        for name in CMAKE_ENV {
            println!("cargo:rerun-if-env-changed={name}");
            std::hash::Hash::hash(&(name, env::var_os(name)), &mut config);
        }
        let gcc = riscv_gcc(&toolchain_dir);
        std::hash::Hash::hash(&gcc, &mut config);
        let key = format!(
            "{}-{:016x}",
            self.name(),
            std::hash::Hasher::finish(&config)
        );

        // Match CMake's compiler selection so ambient CC/CXX cannot change
        // the flags cmake-rs derives from the compiler family.
        let cxx = gcc.with_file_name(
            gcc.file_name()
                .unwrap()
                .to_str()
                .unwrap()
                .trim_end_matches("gcc")
                .to_owned()
                + "g++",
        );
        let mut c_cfg = cc::Build::new();
        c_cfg.compiler(&gcc);
        let mut cxx_cfg = cc::Build::new();
        cxx_cfg.compiler(cxx);
        let mut cfg = cmake::Config::new(&guest_dir);
        cfg.init_c_cfg(c_cfg).init_cxx_cfg(cxx_cfg);
        cfg.out_dir(
            PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR unset"))
                .join("guest-build")
                .join(&key),
        );
        // Set the guest triple explicitly so cmake-rs selects RISC-V flags
        // even if the calling crate targets the host (e.g. -m64).
        // The guest CMakeLists.txt supplies the remaining bare-metal flags.
        cfg.target(self.guest_triple())
            .profile("Release")
            .build_target(&self.guest_target());
        for (name, value) in &defines {
            cfg.define(name, value);
        }

        cfg.define(
            "MONAD_ZKVM_GIT_COMMIT",
            env::var("MONAD_ZKVM_GIT_COMMIT").unwrap_or_default(),
        )
        .define(
            "MONAD_ZKVM_BUILD_ID",
            env::var("MONAD_ZKVM_BUILD_ID").unwrap_or_else(|_| "none".into()),
        );

        cfg.build().join("build")
    }

    /// Build the guest archive and emit Cargo link directives. The backend's
    /// Rust entrypoint crate (e.g. `ziskos`) supplies `_start`.
    pub fn build_guest_lib(self) {
        let build_dir = self.build_guest_archive();

        match self {
            Self::Zisk => {
                let align_ld = manifest_dir().join("align.ld");
                println!("cargo:rerun-if-changed={}", align_ld.display());
                println!("cargo:rustc-link-arg=-T{}", align_ld.display());
            }
        }
        println!("cargo:rustc-link-arg=--gc-sections");
        println!("cargo:rustc-link-search=native={}", build_dir.display());
        println!("cargo:rustc-link-lib=static={}", self.guest_target());
    }
}

/// The ZisK compiler options, read from the environment and OFF by default.
/// The reference Nix build turns all of them on.
const ZISK_OPTIONS: [&str; 2] = ["MONAD_ZKVM_ZISK_DMA", "MONAD_ZKVM_ZISK_LTO"];

/// Environment variables cmake-rs reads for the guest build.
const CMAKE_ENV: [&str; 3] = ["CMAKE", "CMAKE_GENERATOR", "CMAKE_PREFIX_PATH"];

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
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_BUILD_ID");
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_GIT_COMMIT");
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
        "category",
        "cmake",
        // Vendored sources on the guest include path. third_party/ as a whole
        // is not watched: it holds large test-suite submodules the guest
        // never reads.
        "third_party/blst",
        "third_party/cthash",
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
    for prefix in [
        "riscv64-none-elf-",
        "riscv64-unknown-elf-",
        "riscv-none-elf-",
    ] {
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
