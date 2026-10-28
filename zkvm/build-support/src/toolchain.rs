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

use std::{path::Path, process::Command};

pub(super) fn fingerprint(gcc: &Path) -> String {
    for var in ["PATH", "GCC_EXEC_PREFIX", "COMPILER_PATH"] {
        println!("cargo:rerun-if-env-changed={var}");
    }
    let script = Path::new(env!("CARGO_MANIFEST_DIR")).join("toolchain.py");
    println!("cargo:rerun-if-changed={}", script.display());
    let out = Command::new("python3")
        .arg(&script)
        .arg(gcc)
        .arg("--watch-paths")
        .output()
        .expect("Python 3 is required to fingerprint the guest toolchain");
    assert!(
        out.status.success(),
        "cannot fingerprint {}: {}",
        gcc.display(),
        String::from_utf8_lossy(&out.stderr)
    );
    let output = String::from_utf8(out.stdout).expect("toolchain.py output is not UTF-8");
    // The first line is the digest; the remaining lines identify Cargo inputs.
    let mut lines = output.lines();
    let digest = lines.next().expect("toolchain.py returned no fingerprint");
    assert!(
        digest.len() == 64 && digest.bytes().all(|b| b.is_ascii_hexdigit()),
        "invalid toolchain fingerprint: {digest}"
    );
    for path in lines {
        println!("cargo:rerun-if-changed={path}");
    }
    digest.to_owned()
}
