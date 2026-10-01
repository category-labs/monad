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
            for option in ZISK_OPTIONS {
                println!("cargo:rerun-if-env-changed={option}");
                defines.push((
                    option.into(),
                    env::var(option).unwrap_or_else(|_| "OFF".into()),
                ));
            }
        }
        defines.extend(extra_cmake_definitions());

        // Reuse objects across commits, but not after a compiler rebuild, and
        // give each configuration a cache of its own: switching back to one is
        // free, and a definition dropped from a set cannot linger in
        // CMakeCache. The commit stamp stays out of the key. Keep the caches
        // in Cargo's OUT_DIR so independent builds cannot share them.
        let mut config = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(&defines, &mut config);
        for name in build_env_names(self.guest_triple()) {
            println!("cargo:rerun-if-env-changed={name}");
            std::hash::Hash::hash(&(&name, env::var_os(&name)), &mut config);
        }
        let gcc = riscv_gcc(&toolchain_dir);
        let key = format!(
            "{}-{}-{:016x}",
            self.name(),
            toolchain::fingerprint(&gcc),
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
                definitions.iter().rev().find(|(key, _)| key == name)
                    .is_some_and(|(_, value)| matches!(
                        value.to_ascii_uppercase().as_str(),
                        "1" | "ON" | "YES" | "TRUE" | "Y"
                    ))
            };
            if !enabled("MONAD_ZKVM_SELFTEST") || enabled("MONAD_ZKVM_GAS_SELFTEST") {
                let out_dir =
                    PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR unset"));
                let slots_ld = out_dir.join("slots.ld");
                std::fs::write(&slots_ld, zisk_slots_ld())
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

/// The ZisK compiler options, read from the environment and OFF by default.
/// The reference Nix build turns all of them on.
const ZISK_OPTIONS: [&str; 3] = [
    "MONAD_ZKVM_ZISK_DMA",
    "MONAD_ZKVM_ZISK_CLEAN_BYTE_STORES",
    "MONAD_ZKVM_ZISK_LTO",
];

/// Environment inputs used by cc-rs and cmake-rs, including target overrides.
fn build_env_names(triple: &str) -> Vec<String> {
    let mut names = vec![
        "CRATE_CC_NO_DEFAULTS".to_string(),
        "CC_SHELL_ESCAPED_FLAGS".into(),
    ];
    for flags in [
        "CFLAGS",
        "CXXFLAGS",
        "CMAKE",
        "CMAKE_PREFIX_PATH",
        "CMAKE_GENERATOR",
    ] {
        names.extend([
            flags.to_string(),
            format!("TARGET_{flags}"),
            format!("{flags}_{triple}"),
            format!("{flags}_{}", triple.replace('-', "_")),
        ]);
    }
    names
}

fn manifest_dir() -> PathBuf {
    PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR unset"))
}

/// The linker script that lays out the interpreter's handler slots
/// (category/vm/interpreter/execute.cpp): one per revision from BERLIN (8) to
/// AMSTERDAM (15) and per opcode, 4 KiB each, the newest revision first and
/// then in opcode order, so that a handler's address is `monad_vm_slots` plus
/// its offset. A slot holds the handler's six copies (instruction_table.hpp's
/// lag_offset), copies 4, 5, 0, 1, 2 and 3 in address order; each opens with
/// LEAD bytes where PUSH1 and PUSH2 land on the opcode, then the copy. The
/// pairs the landings jump to come past every slot, and so do the handlers
/// too large for a copy, whose copies jump there. The gaps are nops. A
/// landing longer than LEAD or a copy that outgrows its region fails the link,
/// since the location counter cannot move backwards, and so does a region left
/// without a landing, or a copy that does not start right after its landing.
fn zisk_slots_ld() -> String {
    const SLOT: usize = 0x1000;
    // instruction_table.hpp's copies, in address order: where each copy's
    // 184-byte lead starts in its slot, its sections' suffix, and the copy's.
    const COPIES: [(usize, &str, &str); 6] = [
        (0, "_4", "4"),
        (684, "_5", "5"),
        (1368, "", ""),
        (2048, "_1", "1"),
        (2728, "_2", "2"),
        (3412, "_3", "3"),
    ];
    const LEAD: usize = 0xb8;
    let mut ld = String::from(
        "SECTIONS {\n    .monad_vm_slots : ALIGN(0x400) {\n        \
         FILL(0x13000000)\n        monad_vm_slots = .;\n",
    );
    for (rank, rev) in (8..=15).rev().enumerate() {
        for op in 0..256 {
            let at = (rank * 256 + op) * SLOT;
            for (start, sections, copy) in COPIES {
                let lead = at + start;
                let entry = lead + LEAD;
                let symbol = if copy.is_empty() {
                    String::new()
                } else {
                    format!("_{copy}")
                };
                ld += &format!(
                    "        . = monad_vm_slots + {lead:#x};\n        \
                     KEEP(*(.monad_vm_lead{sections}.{rev:02}.{op:02x}))\n        \
                     ASSERT(. > monad_vm_slots + {lead:#x}, \
                     \"monad_vm_slots: slot {rev:02}.{op:02x}{symbol} has no landing\")\n        \
                     . = monad_vm_slots + {entry:#x};\n        \
                     KEEP(*(.monad_vm_slot{copy}.{rev:02}.{op:02x}))\n        \
                     ASSERT(monad_vm_slot_{rev:02}_{op:02x}{symbol} == monad_vm_slots + {entry:#x}, \
                     \"monad_vm_slots: handler {rev:02}.{op:02x}{symbol} is not after its landing\")\n"
                );
            }
        }
    }
    // The pairs the landings jump to, and the handlers too large for a copy,
    // past every slot.
    ld += &format!(
        "        . = monad_vm_slots + {:#x};\n        \
         KEEP(*(.monad_vm_push1*))\n        \
         KEEP(*(.monad_vm_push2*))\n        \
         KEEP(*(.monad_vm_swap1*))\n        \
         KEEP(*(.monad_vm_dup*))\n        \
         KEEP(*(.monad_vm_swapn*))\n        \
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

/// Further CMake definitions for a development build, from
/// MONAD_ZKVM_CMAKE_ARGS as shell-quoted `-DNAME=VALUE` words. The reference
/// Nix build sets none.
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
            // Keep the selected tools consistent with the fingerprint and watch list.
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
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_CMAKE_ARGS");
    println!("cargo:rerun-if-env-changed=RISCV_TOOLCHAIN_DIR");
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_BUILD_ID");
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

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn cmake_definitions_preserve_argument_boundaries() {
        let args = r#"'-DCMAKE_CXX_FLAGS=-O2 -g' '-DPATH:PATH=/tmp/with spaces' '-DNOTE=it'"'"'s \"quoted\"' '-DEMPTY=' '-DLIST=a;b'"#;
        assert_eq!(
            parse_cmake_definitions(args),
            vec![
                ("CMAKE_CXX_FLAGS".into(), "-O2 -g".into()),
                ("PATH".into(), "/tmp/with spaces".into()),
                ("NOTE".into(), r#"it's \"quoted\""#.into()),
                ("EMPTY".into(), "".into()),
                ("LIST".into(), "a;b".into()),
            ]
        );
        assert!(parse_cmake_definitions("  ").is_empty());
        assert_eq!(
            parse_cmake_definitions("-DFOO=ON"),
            vec![("FOO".into(), "ON".into())]
        );
    }

    #[test]
    #[should_panic(expected = "invalid quoting")]
    fn cmake_definitions_reject_unclosed_quotes() {
        parse_cmake_definitions("'-DFOO=ON");
    }

    #[test]
    fn rejects_toolchain_selection_overrides() {
        for name in [
            "RISCV_TOOLCHAIN_DIR",
            "RISCV_PREFIX",
            "CMAKE_TOOLCHAIN_FILE",
            "CMAKE_C_COMPILER",
            "CMAKE_CXX_COMPILER",
            "CMAKE_ASM_COMPILER",
            "CMAKE_C_COMPILER_LAUNCHER",
            "CMAKE_CXX_COMPILER_AR",
            "CMAKE_AR",
            "CMAKE_RANLIB",
            "CMAKE_LINKER",
        ] {
            for suffix in ["", ":FILEPATH"] {
                let args = format!("-D{name}{suffix}=/other/toolchain");
                assert!(
                    std::panic::catch_unwind(|| parse_cmake_definitions(&args)).is_err(),
                    "{args}"
                );
            }
        }
    }

    #[test]
    fn accepts_cmake_compiler_prefixes_in_order() {
        let dir = test_dir("monad-gcc-prefixes");
        let bin = dir.join("bin");
        fs::create_dir_all(&bin).unwrap();
        let prefixes = [
            "riscv64-none-elf-",
            "riscv64-unknown-elf-",
            "riscv-none-elf-",
        ];
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

#[cfg(all(test, unix))]
mod build_tests;

/// A fresh directory for one test. The clock cannot name it: tests run in
/// parallel, and macOS reports time in microseconds.
#[cfg(test)]
fn test_dir(label: &str) -> PathBuf {
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = env::temp_dir().join(format!(
        "{label}-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    // A run that died left it behind under a pid that was reused.
    let _ = std::fs::remove_dir_all(&dir);
    dir
}
