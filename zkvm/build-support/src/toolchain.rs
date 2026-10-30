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

use std::{
    collections::hash_map::DefaultHasher,
    env,
    fs::File,
    hash::{Hash, Hasher},
    io::Read,
    path::{Path, PathBuf},
    process::Command,
    thread,
};

/// Fingerprint the tools a guest build runs: the drivers, GCC's frontends,
/// the assembler and the archive tools, by path, symlink target and content.
/// Rebuilding a frontend need not change the driver.
pub(super) fn fingerprint(gcc: &Path) -> String {
    for var in ["PATH", "GCC_EXEC_PREFIX", "COMPILER_PATH"] {
        println!("cargo:rerun-if-env-changed={var}");
    }
    let name = gcc
        .file_name()
        .and_then(|n| n.to_str())
        .expect("gcc path is utf-8");
    let prefix = name.strip_suffix("gcc").expect("compiler name ends in gcc");
    let cxx = gcc.with_file_name(format!("{prefix}g++"));
    let mut files = vec![gcc.to_path_buf(), cxx.clone()];
    for (driver, program) in [(gcc, "cc1"), (cxx.as_path(), "cc1plus"), (gcc, "as")] {
        files.push(locate(driver, program));
    }
    files.extend(["ar", "ranlib"].map(|tool| gcc.with_file_name(format!("{prefix}{tool}"))));

    // Build scripts are unoptimised: hash the files in parallel.
    let digests: Vec<u64> = thread::scope(|scope| {
        let handles: Vec<_> = files
            .iter()
            .map(|path| scope.spawn(move || hash_file(path)))
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("hashing thread panicked"))
            .collect()
    });

    // Watch the directory too: a higher-priority compiler prefix may appear.
    println!(
        "cargo:rerun-if-changed={}",
        gcc.parent().expect("gcc has a directory").display()
    );
    let mut hasher = DefaultHasher::new();
    for (path, digest) in files.iter().zip(digests) {
        // Watch and hash both the symlink path and its target.
        let target = path
            .canonicalize()
            .unwrap_or_else(|e| panic!("cannot resolve {}: {e}", path.display()));
        for name in [path, &target] {
            println!("cargo:rerun-if-changed={}", name.display());
            name.hash(&mut hasher);
        }
        digest.hash(&mut hasher);
    }
    format!("{:016x}", hasher.finish())
}

/// Resolve the program a GCC driver runs, as `-print-prog-name` names it.
fn locate(driver: &Path, program: &str) -> PathBuf {
    let out = Command::new(driver)
        .arg(format!("-print-prog-name={program}"))
        .output()
        .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", driver.display()));
    assert!(
        out.status.success(),
        "{} cannot locate {program}",
        driver.display()
    );
    let name = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    if name.is_file() {
        return name;
    }
    // A bare name is searched on PATH, as the driver would.
    env::var_os("PATH")
        .iter()
        .flat_map(env::split_paths)
        .map(|dir| dir.join(&name))
        .find(|path| path.is_file())
        .unwrap_or_else(|| panic!("cannot locate {program}: {}", name.display()))
}

fn hash_file(path: &Path) -> u64 {
    let mut file =
        File::open(path).unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
    let mut hasher = DefaultHasher::new();
    let mut buf = vec![0; 1 << 20];
    loop {
        let n = file
            .read(&mut buf)
            .unwrap_or_else(|e| panic!("cannot read {}: {e}", path.display()));
        if n == 0 {
            return hasher.finish();
        }
        hasher.write(&buf[..n]);
    }
}

#[cfg(all(test, unix))]
mod tests {
    use super::*;
    use std::{fs, os::unix::fs::PermissionsExt};

    /// A fake toolchain whose drivers name their programs beside `bin/`.
    struct Fake {
        root: PathBuf,
        gcc: PathBuf,
    }

    impl Fake {
        fn new() -> Self {
            let root = crate::test_dir("monad-toolchain");
            let bin = root.join("bin");
            fs::create_dir_all(&bin).unwrap();
            for driver in ["gcc", "g++"] {
                let path = bin.join(format!("riscv-none-elf-{driver}"));
                fs::write(&path, "#!/bin/sh\nprintf '%s/../%s\\n' \"$(dirname \"$0\")\" \"${1#-print-prog-name=}\"\n").unwrap();
                fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
            }
            for name in Self::COMPONENTS {
                fs::write(root.join(name), "version 1").unwrap();
            }
            let gcc = bin.join("riscv-none-elf-gcc");
            Self { root, gcc }
        }

        const COMPONENTS: [&'static str; 5] = [
            "cc1",
            "cc1plus",
            "as",
            "bin/riscv-none-elf-ar",
            "bin/riscv-none-elf-ranlib",
        ];

        fn fingerprint(&self) -> String {
            fingerprint(&self.gcc)
        }
    }

    impl Drop for Fake {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }

    #[test]
    fn every_component_is_hashed() {
        let fake = Fake::new();
        let original = fake.fingerprint();
        assert_eq!(fake.fingerprint(), original);
        // Same path, same size: only the content changes.
        for name in Fake::COMPONENTS {
            let path = fake.root.join(name);
            fs::write(&path, "version 2").unwrap();
            assert_ne!(fake.fingerprint(), original, "{name}");
            fs::write(&path, "version 1").unwrap();
            assert_eq!(fake.fingerprint(), original, "{name}");
        }
        let cxx = fake.root.join("bin/riscv-none-elf-g++");
        let mut driver = fs::read_to_string(&cxx).unwrap();
        driver.push_str("# rebuilt driver\n");
        fs::write(&cxx, driver).unwrap();
        assert_ne!(fake.fingerprint(), original);
    }

    #[test]
    fn symlink_target_is_tracked() {
        let fake = Fake::new();
        let link = fake.root.join("cc1plus");
        let target = fake.root.join("cc1plus-real");
        fs::write(&target, "version 1").unwrap();
        fs::remove_file(&link).unwrap();
        std::os::unix::fs::symlink(&target, &link).unwrap();
        let original = fake.fingerprint();
        // A rebuilt frontend with the same content, installed beside the old one.
        let rebuilt = fake.root.join("cc1plus-rebuilt");
        fs::write(&rebuilt, "version 1").unwrap();
        fs::remove_file(&link).unwrap();
        std::os::unix::fs::symlink(&rebuilt, &link).unwrap();
        assert_ne!(fake.fingerprint(), original);
    }

    #[test]
    #[should_panic(expected = "cannot locate cc1plus")]
    fn missing_component_fails() {
        let fake = Fake::new();
        fs::remove_file(fake.root.join("cc1plus")).unwrap();
        fake.fingerprint();
    }
}
