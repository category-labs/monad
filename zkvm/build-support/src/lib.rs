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
            Self::Sp1 => "monad-zkvm-guest-sp1",
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
        if let Self::Zisk = self {
            for (option, default) in ZISK_OPTIONS {
                println!("cargo:rerun-if-env-changed={option}");
                defines.push((
                    option.into(),
                    env::var(option).unwrap_or_else(|_| default.into()),
                ));
            }
        }

        println!("cargo:rerun-if-env-changed=MONAD_ZKVM_CMAKE_ARGS");
        defines.extend(extra_cmake_definitions());

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
        // SP1's caller targets the host. Set the guest triple explicitly so
        // cmake-rs selects RISC-V flags instead of host flags such as -m64.
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

    /// Build the guest archive and emit Cargo link directives.
    /// Used by ZisK, where `ziskos` supplies `_start`.
    pub fn build_guest_lib(self) {
        let build_dir = self.build_guest_archive();

        if let Self::Zisk = self {
            let align_ld = manifest_dir().join("align.ld");
            println!("cargo:rerun-if-changed={}", align_ld.display());
            println!("cargo:rustc-link-arg=-T{}", align_ld.display());

            // The state-only self-test does not link the interpreter.
            let definitions = extra_cmake_definitions();
            let enabled = |name: &str| {
                definitions
                    .iter()
                    .rev()
                    .find(|(key, _)| key == name)
                    .is_some_and(|(_, value)| {
                        matches!(
                            value.to_ascii_uppercase().as_str(),
                            "1" | "ON" | "YES" | "TRUE" | "Y"
                        )
                    })
            };
            if !enabled("MONAD_ZKVM_SELFTEST") || enabled("MONAD_ZKVM_GAS_SELFTEST") {
                let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR unset"));
                let slots_ld = out_dir.join("slots.ld");
                let prefix_enabled = |file| {
                    let path = build_dir.join(file);
                    match std::fs::read_to_string(&path).as_deref() {
                        Ok("1") => true,
                        Ok("0") => false,
                        other => panic!(
                            "invalid prefix configuration in {}: {other:?}",
                            path.display()
                        ),
                    }
                };
                std::fs::write(
                    &slots_ld,
                    zisk_slots_ld(
                        prefix_enabled("swap1-prefix.enabled"),
                        prefix_enabled("dup-prefix.enabled"),
                        prefix_enabled("swapn-prefix.enabled"),
                        prefix_enabled("comparison-prefix.enabled"),
                    ),
                )
                .expect("write slots.ld");
                println!(
                    "cargo:rustc-link-arg-bin=monad-zkvm-zisk=-T{}",
                    slots_ld.display()
                );
            }
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

/// ZisK build options accepted directly from the environment and their defaults.
const ZISK_OPTIONS: [(&str, &str); 9] = [
    ("MONAD_ZKVM_ZISK_DMA", "OFF"),
    ("MONAD_ZKVM_ZISK_LTO", "OFF"),
    ("MONAD_ZKVM_FUSE_DUP", "ON"),
    ("MONAD_ZKVM_FUSE_COMPARISON", "ON"),
    ("MONAD_ZKVM_FUSE_SWAPN", "ON"),
    ("MONAD_ZKVM_FUSE_SWAP1", "ON"),
    ("MONAD_ZKVM_FUSE_SOLIDITY_SELECTOR", "ON"),
    ("MONAD_ZKVM_FUSE_SOLIDITY_ALLOC_FINALIZE", "ON"),
    ("MONAD_ZKVM_FUSE_SOLIDITY_COPY_LOOP", "ON"),
];

/// Environment variables cmake-rs reads for the guest build.
const CMAKE_ENV: [&str; 3] = ["CMAKE", "CMAKE_GENERATOR", "CMAKE_PREFIX_PATH"];

fn manifest_dir() -> PathBuf {
    PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR unset"))
}

/// Lay out 4-KiB opcode slots, newest revision first. Each copy has 64 bytes for overflow
/// and PUSH prefixes, 28 for enabled comparisons, and 40 per enabled swap or DUP family.
/// Fused pairs and oversized handlers follow the slots. The linker rejects
/// misplaced entries and copies that exceed their region.
fn zisk_slots_ld(
    fuse_swap1: bool,
    fuse_dup: bool,
    fuse_swapn: bool,
    fuse_comparison: bool,
) -> String {
    const SLOT: usize = 0x1000;
    // Prefix-region offset, prefix-section suffix, and handler-section suffix.
    // Keep these offsets in sync with instruction_table.hpp::lag_offset.
    let copies: &[(usize, &str, &str)] = if fuse_dup {
        &[
            (0, "_4", "4"),
            (684, "_5", "5"),
            (1368, "", ""),
            (2048, "_1", "1"),
            (2728, "_2", "2"),
            (3412, "_3", "3"),
        ]
    } else {
        &[
            (0, "_4", "4"),
            (584, "_5", "5"),
            (1168, "_6", "6"),
            (if fuse_swap1 { 1760 } else { 1752 }, "", ""),
            (2336, "_1", "1"),
            (2920, "_2", "2"),
            (3504, "_3", "3"),
        ]
    };
    let prefix_size = 64
        + 28 * usize::from(fuse_comparison)
        + 40 * usize::from(fuse_swapn)
        + 40 * usize::from(fuse_swap1)
        + 40 * usize::from(fuse_dup);
    let mut ld = String::from(
        "SECTIONS {\n    .monad_vm_slots : ALIGN(0x400) {\n        \
         FILL(0x13000000)\n        monad_vm_slots = .;\n",
    );
    for (rank, rev) in (8..=15).rev().enumerate() {
        for op in 0..256 {
            let slot_address = (rank * 256 + op) * SLOT;
            for &(copy_offset, prefix_suffix, handler_suffix) in copies {
                let prefix_address = slot_address + copy_offset;
                let handler_address = prefix_address + prefix_size;
                let symbol_suffix = if handler_suffix.is_empty() {
                    String::new()
                } else {
                    format!("_{handler_suffix}")
                };
                ld += &format!(
                    "        . = monad_vm_slots + {prefix_address:#x};\n        \
                     KEEP(*(.monad_vm_lead{prefix_suffix}.{rev:02}.{op:02x}))\n        \
                     ASSERT(. > monad_vm_slots + {prefix_address:#x}, \
                     \"monad_vm_slots: slot {rev:02}.{op:02x}{symbol_suffix} has no landing\")\n        \
                     . = monad_vm_slots + {handler_address:#x};\n        \
                     KEEP(*(.monad_vm_slot{handler_suffix}.{rev:02}.{op:02x}))\n        \
                     ASSERT(monad_vm_slot_{rev:02}_{op:02x}{symbol_suffix} == monad_vm_slots + {handler_address:#x}, \
                     \"monad_vm_slots: handler {rev:02}.{op:02x}{symbol_suffix} is not after its landing\")\n"
                );
            }
        }
    }
    // Fused pairs and oversized handlers live outside the fixed-size slots.
    ld += &format!(
        "        . = monad_vm_slots + {:#x};\n        \
         KEEP(*(.monad_vm_push1*))\n        \
         KEEP(*(.monad_vm_push2*))\n        \
         KEEP(*(.monad_vm_swap1*))\n        \
         KEEP(*(.monad_vm_bool*))\n        \
         KEEP(*(.monad_vm_swapn*))\n        \
         KEEP(*(.monad_vm_dup*))\n        \
         KEEP(*(.monad_vm_body*))\n    }}\n}} INSERT AFTER .text;\n",
        8 * 256 * SLOT
    );
    ld
}

fn locate_repo_root(manifest: &Path) -> PathBuf {
    manifest
        .ancestors()
        .find(|p| p.join("zkvm/guest/CMakeLists.txt").exists())
        .expect("failed to locate monad repo root from build.rs CARGO_MANIFEST_DIR")
        .to_path_buf()
}

fn extra_cmake_definitions() -> Vec<(String, String)> {
    let Ok(args) = env::var("MONAD_ZKVM_CMAKE_ARGS") else {
        return Vec::new();
    };
    parse_cmake_definitions(&args)
}

fn parse_cmake_definitions(args: &str) -> Vec<(String, String)> {
    let words = shlex::split(args).expect("invalid quoting in MONAD_ZKVM_CMAKE_ARGS");
    words
        .iter()
        .map(|word| {
            let def = word.strip_prefix("-D").unwrap_or_else(|| {
                panic!("MONAD_ZKVM_CMAKE_ARGS takes -DNAME=VALUE words, got `{word}`")
            });
            let (name, value) = def.split_once('=').unwrap_or_else(|| {
                panic!("MONAD_ZKVM_CMAKE_ARGS takes -DNAME=VALUE words, got `{word}`")
            });
            // -DNAME:TYPE=VALUE: cmake-rs takes the name alone.
            let name = name.split(':').next().unwrap_or(name);
            // Keep CMake and cmake-rs on the same selected toolchain.
            assert!(
                !matches!(
                    name,
                    "RISCV_TOOLCHAIN_DIR"
                        | "RISCV_PREFIX"
                        | "CMAKE_TOOLCHAIN_FILE"
                        | "CMAKE_AR"
                        | "CMAKE_RANLIB"
                        | "CMAKE_LINKER"
                ) && !["CMAKE_C_COMPILER", "CMAKE_CXX_COMPILER", "CMAKE_ASM_COMPILER"]
                    .iter()
                    .any(|prefix| name.starts_with(prefix)),
                "{name} cannot be overridden with -D; select the toolchain with the RISCV_TOOLCHAIN_DIR environment variable"
            );
            (name.to_string(), value.to_string())
        })
        .collect()
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
        "third_party/ethash_vendor",
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
