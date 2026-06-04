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

//! Shared cmake-driver logic for the ZisK and SP1 guest build.rs files.
//!
//! Both crates drive `zkvm/guest/CMakeLists.txt` directly as the top-level
//! CMake project. The only backend-distinguishing cmake input is
//! `MONAD_ZKVM_GUEST_TARGET` (`zisk` or `sp1`) — the cmake derives the target
//! name (`monad-zkvm-guest-<suffix>`) and the per-backend mirror include
//! directory (`zkvm/<suffix>/`) from that. Backends also differ in RISC-V
//! march/flags and a couple of linker args, handled here. Consumer build.rs
//! files just call `Backend::Zisk.build_guest_lib()` (or `Sp1`).

use std::{env, path::{Path, PathBuf}, process::Command};

// SP1 v6's RISC-V profile is rv64im (no atomics); ZisK's is rv64ima. The
// default zkvm/ toolchain file picks rv64ima, so for SP1 we override the
// CMAKE_*_FLAGS_INIT block.
const SP1_C_FLAGS: &str = "-march=rv64im -mabi=lp64 -mcmodel=medany \
    -nostartfiles -ffunction-sections -fdata-sections";
const SP1_CXX_FLAGS: &str = "-march=rv64im -mabi=lp64 -mcmodel=medany \
    -nostartfiles -nostdlib++ -fno-exceptions -fno-rtti \
    -ffunction-sections -fdata-sections";
const SP1_ASM_FLAGS: &str = "-march=rv64im -mabi=lp64";

#[derive(Clone, Copy, Debug)]
pub enum Backend {
    Zisk,
    Sp1,
}

impl Backend {
    /// Short suffix used as the cmake `MONAD_ZKVM_GUEST_TARGET` value and
    /// as the per-backend mirror-directory name under `zkvm/`.
    fn name(self) -> &'static str {
        match self {
            Self::Zisk => "zisk",
            Self::Sp1 => "sp1",
        }
    }

    /// Fully-qualified cmake target name produced by
    /// `zkvm/guest/CMakeLists.txt` for this backend.
    fn guest_target(self) -> String {
        format!("monad-zkvm-guest-{}", self.name())
    }

    /// The RISC-V guest target triple for this backend. Passed to cmake-rs via
    /// `Config::target` so it treats this as a cross build and does NOT inject
    /// host flags like `-m64` into the compiler probe. This matters because the
    /// SP1 path drives cmake from the host-target `script` crate (cargo's
    /// `TARGET` is the host there); the ZisK path already builds under this
    /// triple, so setting it explicitly is a harmless no-op for ZisK.
    fn guest_triple(self) -> &'static str {
        match self {
            Self::Zisk => "riscv64ima-zisk-zkvm-elf",
            Self::Sp1 => "riscv64im-succinct-zkvm-elf",
        }
    }

    /// Drive the zkvm/ CMake project to build
    /// `libmonad-zkvm-guest-<backend>.a` for this backend and return the
    /// directory containing the archive.
    ///
    /// Always cross-compiles to RISC-V. Host x86 iteration goes through the
    /// `monad-zkvm-x86-test-runner` executable produced by the main host
    /// CMake build, not through cargo.
    ///
    /// Caller's `CARGO_MANIFEST_DIR` is used to locate the repo root.
    fn build_guest_archive(self) -> PathBuf {
        let manifest = manifest_dir();
        let repo_root = locate_repo_root(&manifest);
        let zkvm_dir = repo_root.join("zkvm");
        let guest_dir = zkvm_dir.join("guest");
        let toolchain =
            repo_root.join("category/core/toolchains/riscv64-elf.cmake");

        emit_rerun_directives(&zkvm_dir, &repo_root);

        let mut cfg = cmake::Config::new(&guest_dir);
        cfg.target(self.guest_triple())
            .define("MONAD_ZKVM_GUEST_TARGET", self.name())
            .define("CMAKE_TOOLCHAIN_FILE", &toolchain)
            .define("RISCV_TOOLCHAIN_DIR", riscv_toolchain_dir())
            .profile("Release")
            .build_target(&self.guest_target());

        // cmake-rs forces CMAKE_PREFIX_PATH="" (env) to keep host-build paths
        // from leaking in; we still need find_package(Boost CONFIG) to locate
        // the host BoostConfig.cmake (Boost.Outcome is the only header-only
        // Boost piece we use). Pass it as a cmake variable instead, which
        // takes precedence over the env wipe.
        let prefix_path = env::var("CMAKE_PREFIX_PATH").unwrap_or_else(|_| {
            "/usr".to_string()
        });
        cfg.define("CMAKE_PREFIX_PATH", &prefix_path);

        if let Self::Sp1 = self {
            cfg.define("CMAKE_C_FLAGS_INIT", SP1_C_FLAGS)
                .define("CMAKE_CXX_FLAGS_INIT", SP1_CXX_FLAGS)
                .define("CMAKE_ASM_FLAGS_INIT", SP1_ASM_FLAGS);
        }

        let dst = cfg.build();
        // guest/ is the cmake project root, so the static archive ends up
        // directly in <dst>/build/, not in a guest/ subdir.
        dst.join("build")
    }

    /// Build the guest archive and emit the `cargo:rustc-link-*` directives
    /// to link it into the consuming Rust crate. Used by the ZisK guest crate,
    /// whose `_start` is provided by `ziskos` and linked by rustc.
    pub fn build_guest_lib(self) {
        let build_dir = self.build_guest_archive();

        match self {
            Self::Zisk => {
                let align_ld = manifest_dir().join("align.ld");
                println!("cargo:rustc-link-arg=-T{}", align_ld.display());
            }
            Self::Sp1 => {}
        }
        println!("cargo:rustc-link-arg=--gc-sections");
        println!(
            "cargo:rustc-link-search=native={}",
            build_dir.display()
        );
        println!("cargo:rustc-link-lib=static={}", self.guest_target());
    }

    /// SP1 full-SDK link. Build the guest archive, compile the entry
    /// `program/main.c` with the same RISC-V GCC the cmake build uses, then
    /// link `main.o` + the guest archive + `libzkevm.a` against `zkvm.ld` via
    /// `ld.lld`. Returns the path to the resulting guest ELF.
    ///
    /// `libzkevm.a` is built from source from the SP1 zkEVM SDK's
    /// `zkevm/libzkevm-cabi` staticlib crate (found in the `sp1-build` git
    /// checkout) rather than vendored as a binary blob; `zkvm.ld` and the
    /// accelerator header come from the same SP1 source. Unlike the ZisK path
    /// there is no Rust guest crate: `libzkevm.a` supplies `_start`, the
    /// allocator, the IO ABI, and every accelerator.
    pub fn build_guest_elf(self) -> PathBuf {
        assert!(matches!(self, Self::Sp1), "build_guest_elf is SP1-only");

        let repo_root = locate_repo_root(&manifest_dir());
        let gcc = riscv_gcc(&riscv_toolchain_dir());

        let build_dir = self.build_guest_archive();
        let archive = build_dir.join(format!("lib{}.a", self.guest_target()));

        // Build libzkevm.a from source (SP1's zkevm/libzkevm-cabi staticlib
        // crate) via the SP1 SDK's own helper, and take the accelerator header
        // from the same SP1 zkevm/ source tree.
        let zkevm = sp1_zkevm_dir();
        let libzkevm = sp1_build::build_program_staticlib(
            zkevm.join("libzkevm-cabi").to_str().expect("cabi path is utf-8"),
        );
        let include = zkevm.join("include");

        let main_c = repo_root.join("zkvm/sp1/program/main.c");
        let out_dir = PathBuf::from(env::var_os("OUT_DIR").expect("OUT_DIR unset"));
        let main_o = out_dir.join("main.o");
        let elf = out_dir.join("monad-zkvm-guest-sp1.elf");

        // The upstream zkvm.ld targets Rust guests, whose `_start` never runs
        // `.init_array`. The C++ guest's main.c runs the static constructors
        // itself (RLP encoder tables, commit_builder/partial_trie_db statics,
        // ...) via boundary symbols, so inject a `.init_array` section into the
        // upstream script (kept otherwise verbatim from source) before `.data`.
        let zkvm_ld = out_dir.join("zkvm.ld");
        patch_zkvm_ld(&zkevm.join("zkvm.ld"), &zkvm_ld);

        println!("cargo:rerun-if-changed={}", main_c.display());

        // 1) Compile main.c -> main.o with the RISC-V GCC (rv64im / lp64),
        //    matching the flags the cmake guest build uses for SP1.
        let status = Command::new(&gcc)
            .args([
                "-march=rv64im", "-mabi=lp64", "-mcmodel=medany",
                "-nostdlib", "-ffreestanding", "-fno-builtin",
                "-O2", "-Wall", "-Wextra", "-c",
            ])
            .arg(format!("-I{}", include.display()))
            .arg("-o").arg(&main_o)
            .arg(&main_c)
            .status()
            .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", gcc.display()));
        assert!(status.success(), "gcc failed compiling {}", main_c.display());

        // 2) Link main.o + guest archive + libzkevm.a against zkvm.ld via
        //    ld.lld (the linker libzkevm.a was built/tested with).
        let lld = sp1_build::find_lld().expect(
            "ld.lld not found on PATH and no SP1 toolchain has a bundled copy. \
             Install lld (`apt install lld`) or run `sp1up`.",
        );
        // --gc-sections dead-strips unreachable functions before resolving
        // their references. The guest archive (shared with ZisK) contains code
        // paths unreachable in this guest — e.g. Prague request hashing, Monad
        // staking precompiles — that reference symbols not provided here; GC
        // removes them, exactly as the ZisK rustc link does. Relies on the
        // -ffunction-sections/-fdata-sections in SP1_C/CXX_FLAGS.
        let status = Command::new(&lld)
            .args(["-nostdlib", "-static", "--gc-sections"])
            .arg(format!("-T{}", zkvm_ld.display()))
            .arg("-o").arg(&elf)
            .arg(&main_o)
            .arg(&archive)
            .arg(&libzkevm)
            .status()
            .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", lld.display()));
        assert!(status.success(), "ld.lld failed linking {}", elf.display());

        elf
    }
}

/// Copy the upstream SP1 `zkvm.ld` to `dst`, injecting a `.init_array` section
/// (before `.data`) so the C++ guest's `main()` can run its static
/// constructors — the upstream script targets Rust guests whose `_start`
/// skips `.init_array`. Everything else (RAM layout, symbols) is kept verbatim.
fn patch_zkvm_ld(src: &Path, dst: &Path) {
    let script = std::fs::read_to_string(src)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", src.display()));

    // Inject one contiguous RELRO block before `.data`:
    //   .data.rel.ro, .init_array (+ boundary symbols), .got
    //
    // Two problems this fixes, both because the upstream script targets Rust
    // guests and places neither section:
    //  - `.got`: the C++ guest emits GOT-indirected references (e.g. the
    //    out-of-line intx uint256 divide used by expmod_gas_cost). Without an
    //    explicit placement ld.lld emits `.got` past `_end`/`_heap_start`, and
    //    the first heap allocation clobbers the pointers — turning an indirect
    //    call into a jump to heap garbage (SIGSEGV). Placing it before `.data`
    //    keeps it inside the loaded image, below the heap.
    //  - `.init_array`: the SDK's Rust `_start` never runs it, so the C++ guest
    //    `main()` iterates it via the boundary symbols to run static ctors.
    //
    // The sections are kept adjacent because ld.lld requires the RELRO sections
    // (which `.data.rel.ro`, `.init_array` and `.got` all are) to be contiguous.
    let anchor = "    .data : ALIGN(16)";
    assert!(
        script.contains(anchor),
        "upstream zkvm.ld layout changed ({}): no `{anchor}` to inject before",
        src.display()
    );
    let relro = "\
    .data.rel.ro : ALIGN(16)\n    {\n        \
        *(.data.rel.ro .data.rel.ro.* .gnu.linkonce.d.rel.ro.*)\n    } > RAM\n\n    \
    .init_array : ALIGN(8)\n    {\n        \
        __init_array_start = .;\n        \
        KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*)))\n        \
        KEEP(*(.init_array))\n        \
        __init_array_end = .;\n    } > RAM\n\n    \
    .got : ALIGN(16)\n    {\n        \
        *(.got.plt) *(.igot.plt) *(.got) *(.igot)\n    } > RAM\n\n";

    let patched = script.replacen(anchor, &format!("{relro}{anchor}"), 1);
    std::fs::write(dst, patched)
        .unwrap_or_else(|e| panic!("failed to write {}: {e}", dst.display()));
}

/// Locate the SP1 `zkevm/` source tree inside the `sp1-build` git checkout that
/// cargo fetched for that dependency. cargo checks out the whole SP1 repo, so
/// `zkevm/libzkevm-cabi`, `zkevm/zkvm.ld`, and `zkevm/include/` sit alongside
/// the `crates/build` crate we depend on — no submodule or vendored blob.
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

// Walk upward from the caller's manifest until we find
// `zkvm/guest/CMakeLists.txt`, which marks the monad repo root. Works for
// both zkvm/zisk and zkvm/sp1/program callers.
fn locate_repo_root(manifest: &PathBuf) -> PathBuf {
    let mut p = manifest.as_path();
    loop {
        if p.join("zkvm/guest/CMakeLists.txt").exists() {
            return p.to_path_buf();
        }
        p = p
            .parent()
            .expect("failed to locate monad repo root from build.rs CARGO_MANIFEST_DIR");
    }
}

fn emit_rerun_directives(zkvm_dir: &Path, repo_root: &Path) {
    println!("cargo:rerun-if-changed=build.rs");
    // `rerun-if-changed=<dir>` watches only the directory's own mtime, which
    // doesn't update when files inside are edited. Walk and emit per-file
    // paths so edits to ffi.cpp / headers / cmake actually trigger a rebuild.
    for sub in ["guest", "core", "category"] {
        walk_emit(&zkvm_dir.join(sub));
    }
    walk_emit(&repo_root.join("category"));
    walk_emit(&repo_root.join("cmake"));
}

fn walk_emit(root: &Path) {
    let Ok(entries) = std::fs::read_dir(root) else {
        return;
    };
    for entry in entries.flatten() {
        let Ok(ft) = entry.file_type() else { continue };
        let path = entry.path();
        if ft.is_dir() {
            let name = entry.file_name();
            let s = name.to_string_lossy();
            if s == "target" || s == "build" || s == ".git" {
                continue;
            }
            walk_emit(&path);
        } else if ft.is_file() {
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
}

// The RISC-V GCC toolchain dir, from the RISCV_TOOLCHAIN_DIR env var set in
// the local zkvm/.cargo/config.toml (see zkvm/README.md). Required for both
// backends.
fn riscv_toolchain_dir() -> String {
    let dir = env::var("RISCV_TOOLCHAIN_DIR").unwrap_or_default();
    assert!(
        !dir.is_empty(),
        "RISCV_TOOLCHAIN_DIR is not set. Create zkvm/.cargo/config.toml with \
         `[env] RISCV_TOOLCHAIN_DIR = \"/path/to/riscv_gcc\"` (see zkvm/README.md).",
    );
    dir
}

// Full path to the RISC-V gcc under `<toolchain_dir>/bin`, auto-detecting the
// target prefix the same way category/core/toolchains/riscv64-elf.cmake
// does (riscv64-none-elf- for nix, riscv64-unknown-elf- for ZisK).
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