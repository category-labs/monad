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

use sha2::{Digest, Sha256};
use std::{
    env, fs,
    io::Read,
    path::{Path, PathBuf},
    process::Command,
};

pub(super) fn fingerprint(gcc: &Path) -> String {
    for var in ["PATH", "GCC_EXEC_PREFIX", "COMPILER_PATH"] {
        println!("cargo:rerun-if-env-changed={var}");
    }
    let bin = gcc.parent().unwrap();
    // Also notice a newly installed compiler with a higher-priority prefix.
    println!("cargo:rerun-if-changed={}", bin.display());
    let prefix = gcc
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .strip_suffix("gcc")
        .unwrap();
    let cxx = bin.join(format!("{prefix}g++"));
    let mut files = vec![gcc.to_path_buf(), cxx.clone()];
    for (driver, program) in [(gcc, "cc1"), (cxx.as_path(), "cc1plus"), (gcc, "as")] {
        let out = Command::new(driver)
            .arg(format!("-print-prog-name={program}"))
            .output()
            .unwrap_or_else(|e| panic!("cannot query {}: {e}", driver.display()));
        assert!(
            out.status.success(),
            "cannot locate {program} via {}",
            driver.display()
        );
        let path = PathBuf::from(String::from_utf8(out.stdout).unwrap().trim());
        let path = if path.is_file() {
            path
        } else {
            env::split_paths(&env::var_os("PATH").unwrap_or_default())
                .map(|dir| dir.join(&path))
                .find(|candidate| candidate.is_file())
                .unwrap_or_else(|| panic!("cannot locate {program}: {}", path.display()))
        };
        files.push(path);
    }
    for program in ["ar", "ranlib"] {
        files.push(bin.join(format!("{prefix}{program}")));
    }
    fingerprint_files(&files)
}

fn fingerprint_files(files: &[PathBuf]) -> String {
    let mut hash = Sha256::new();
    for path in files {
        // Watch both the symlink and its target; toolchains often share tools.
        println!("cargo:rerun-if-changed={}", path.display());
        let resolved = path
            .canonicalize()
            .unwrap_or_else(|e| panic!("cannot resolve {}: {e}", path.display()));
        println!("cargo:rerun-if-changed={}", resolved.display());
        for name in [path, &resolved] {
            hash.update(name.as_os_str().as_encoded_bytes());
            hash.update([0]);
        }
        let mut file = fs::File::open(path).unwrap();
        let mut content = Sha256::new();
        let mut buf = [0u8; 64 * 1024];
        loop {
            let n = file.read(&mut buf).unwrap();
            if n == 0 {
                break;
            }
            content.update(&buf[..n]);
        }
        hash.update(content.finalize());
    }
    format!("{:x}", hash.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        sync::atomic::{AtomicUsize, Ordering},
        time::SystemTime,
    };

    struct Fixture(PathBuf);

    impl Fixture {
        fn new() -> Self {
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            let dir = env::temp_dir().join(format!(
                "monad-toolchain-{}-{}-{}",
                std::process::id(),
                SystemTime::now()
                    .duration_since(SystemTime::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }

        fn file(&self, name: &str) -> PathBuf {
            let path = self.0.join(name);
            fs::write(&path, "version 1").unwrap();
            path
        }
    }

    impl Drop for Fixture {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn compiler_replacement_invalidates_the_cache() {
        let fixture = Fixture::new();
        let files = [
            fixture.file("gcc"),
            fixture.file("g++"),
            fixture.file("cc1plus"),
        ];
        let original = fingerprint_files(&files);
        assert_eq!(fingerprint_files(&files), original);
        // Same path and size, different compiler contents.
        fs::write(&files[1], "version 2").unwrap();
        assert_ne!(fingerprint_files(&files), original);
        fs::write(&files[1], "version 1").unwrap();
        assert_eq!(fingerprint_files(&files), original);
        // A rebuilt frontend must invalidate even when the driver is unchanged.
        fs::write(&files[2], "version 2").unwrap();
        assert_ne!(fingerprint_files(&files), original);
    }

    #[cfg(unix)]
    #[test]
    fn follows_replaced_symlink_targets() {
        let fixture = Fixture::new();
        let target = fixture.file("cc1plus-real");
        let link = fixture.0.join("cc1plus");
        std::os::unix::fs::symlink(&target, &link).unwrap();
        let original = fingerprint_files(&[link.clone()]);
        fs::write(target, "version 2").unwrap();
        assert_ne!(fingerprint_files(&[link]), original);
    }

    #[cfg(unix)]
    #[test]
    fn discovers_and_fingerprints_gcc_frontends() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = Fixture::new();
        let bin = fixture.0.join("bin");
        fs::create_dir(&bin).unwrap();
        for driver in ["gcc", "g++"] {
            let path = bin.join(format!("riscv-none-elf-{driver}"));
            fs::write(&path, "#!/bin/sh\nprintf '%s/../%s\\n' \"$(dirname \"$0\")\" \"${1#-print-prog-name=}\"\n").unwrap();
            fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
        }
        for name in [
            "cc1",
            "cc1plus",
            "as",
            "bin/riscv-none-elf-ar",
            "bin/riscv-none-elf-ranlib",
        ] {
            fixture.file(name);
        }
        let gcc = bin.join("riscv-none-elf-gcc");
        let original = fingerprint(&gcc);
        assert_eq!(fingerprint(&gcc), original);
        fs::write(fixture.0.join("cc1plus"), "version 2").unwrap();
        assert_ne!(fingerprint(&gcc), original);
    }
}
