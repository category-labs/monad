// Copyright (C) 2025-26 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

use std::{env, fs, path::PathBuf, process::Command};

pub(super) fn embed_guest() {
    let guest = super::manifest_dir();
    let root = super::locate_repo_root(&guest);
    let target = PathBuf::from(env::var_os("OUT_DIR").unwrap()).join("guest-target");

    super::emit_rerun_directives(&root);
    for path in ["Cargo.toml", "Cargo.lock", "build.rs", "align.ld", "src"] {
        println!("cargo:rerun-if-changed={}", guest.join(path).display());
    }
    for name in ["RISCV_TOOLCHAIN_DIR", "CMAKE_PREFIX_PATH"] {
        println!("cargo:rerun-if-env-changed={name}");
    }

    let mut command = Command::new("cargo");
    command
        .current_dir(&guest)
        .args([
            "+zisk",
            "build",
            "--locked",
            "--release",
            "--features",
            "guest",
            "--bin",
            "monad-zkvm-zisk",
            "--target",
            zisk_build::ZISK_TARGET,
            "--target-dir",
        ])
        .arg(&target)
        .env_remove("RUSTC")
        .env_remove("RUSTC_WRAPPER")
        .env_remove("RUSTC_WORKSPACE_WRAPPER");
    // Match cargo-zisk's linker script, cfg and ISA extensions, excluding
    // host rustflags. Keep the temporary linker script alive until Cargo exits.
    let features = zisk_build::target_features_from_features(None, false);
    let _linker_script =
        zisk_build::apply_guest_rustflags(&mut command, Some(&guest), false, &features)
            .expect("cannot configure ZisK guest build; install the zisk Rust toolchain");
    let status = command.status().expect("cannot run cargo +zisk build");
    assert!(status.success(), "Monad guest build failed: {status}");

    let elf = target
        .join(zisk_build::ZISK_TARGET)
        .join("release/monad-zkvm-zisk");
    println!("cargo:rerun-if-changed={}", elf.display());
    let bytes = fs::read(&elf).expect("cannot read built Monad guest ELF");
    println!("cargo:rustc-env=MONAD_GUEST_ELF={}", elf.display());
    println!(
        "cargo:rustc-env=MONAD_GUEST_ELF_HASH={}",
        blake3::hash(&bytes)
    );
}
