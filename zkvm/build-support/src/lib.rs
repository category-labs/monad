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
    process::{Command, Stdio},
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
        if matches!(self, Self::Zisk) {
            return build_zisk_archive(&repo_root);
        }

        let zkvm_dir = repo_root.join("zkvm");
        let guest_dir = zkvm_dir.join("guest");
        let toolchain = repo_root.join("category/core/toolchains/riscv64-elf.cmake");

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
        // Each set of extra definitions configures a cache of its own: a
        // definition dropped from the set would otherwise stay in CMakeCache.
        let extra = extra_cmake_definitions();
        if !extra.is_empty() {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(&extra, &mut h);
            key.push_str(&format!("-defs{:016x}", std::hash::Hasher::finish(&h)));
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

        cfg.define(
            "MONAD_ZKVM_GIT_COMMIT",
            env::var("MONAD_ZKVM_GIT_COMMIT").unwrap_or_default(),
        )
        .define(
            "MONAD_ZKVM_BUILD_ID",
            env::var("MONAD_ZKVM_BUILD_ID").unwrap_or_else(|_| "none".into()),
        );

        for (name, value) in &extra {
            cfg.define(name, value);
        }

        cfg.build().join("build")
    }

    /// Build the guest archive and emit Cargo link directives.
    /// Used by ZisK, where `ziskos` supplies `_start`.
    pub fn build_guest_lib(self) {
        let build_dir = self.build_guest_archive();
        if let Some(path) = env::var_os("MONAD_ZKVM_ARCHIVE_PATH_FILE") {
            let archive = build_dir.join(format!("lib{}.a", self.guest_target()));
            std::fs::write(path, archive.as_os_str().as_encoded_bytes())
                .expect("cannot report the guest archive path");
        }

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

/// Share ZisK's CMake configuration with the standalone archive build.
fn build_zisk_archive(repo_root: &Path) -> PathBuf {
    let script = repo_root.join("zkvm/build-support/build_archive.py");
    println!("cargo:rerun-if-changed={}", script.display());
    let out = Command::new("python3")
        .arg(script)
        .arg("--cargo")
        .stderr(Stdio::inherit())
        .output()
        .expect("Python 3 is required to build the ZisK archive");
    assert!(out.status.success(), "ZisK archive build failed");
    let output = String::from_utf8(out.stdout).expect("archive build output is not UTF-8");
    let mut lines = output.lines();
    let archive = PathBuf::from(lines.next().expect("archive build returned no path"));
    for directive in lines {
        assert!(directive.starts_with("cargo:"), "invalid build directive");
        println!("{directive}");
    }
    archive
        .parent()
        .expect("archive has no directory")
        .to_path_buf()
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

/// Further CMake definitions for a development build, from
/// MONAD_ZKVM_CMAKE_ARGS as shell-quoted `-DNAME=VALUE` words (build.sh passes
/// its own -D arguments there). The reference Nix build fixes its configuration
/// and refuses them.
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
            (name.to_string(), value.to_string())
        })
        .collect()
}

fn emit_rerun_directives(repo_root: &Path) {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_CMAKE_ARGS");
    println!("cargo:rerun-if-env-changed=MONAD_ZKVM_ARCHIVE_PATH_FILE");
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
    use std::{fs, time::SystemTime};

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
