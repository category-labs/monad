// Copyright (C) 2025 Category Labs, Inc.
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

use std::path::{Path, PathBuf};

use crate::repository_root;

pub struct MonadCxx {
    build: cc::Build,
    repo_root: PathBuf,
}

impl MonadCxx {
    pub fn new(bridge_path: &str) -> Self {
        let repo_root = repository_root();

        let mut build = cxx_build::bridge(bridge_path);

        println!(
            "cargo:rerun-if-changed={}",
            repo_root.join("category").display()
        );

        build
            .std("c++23")
            .include(&repo_root)
            .flag_if_supported("-Wno-missing-field-initializers")
            .flag_if_supported("-Wno-attributes=clang::no_sanitize");

        Self { build, repo_root }
    }

    pub fn file<P>(mut self, path: P) -> Self
    where
        P: AsRef<Path>,
    {
        println!("cargo:rerun-if-changed={}", path.as_ref().display());

        self.build.file(path);
        self
    }

    pub fn includes<S>(mut self, paths: impl IntoIterator<Item = S>) -> Self
    where
        S: AsRef<str>,
    {
        for path in paths {
            let path = self.repo_root.join(path.as_ref());

            println!("cargo:rerun-if-changed={}", path.display());

            self.build.include(path);
        }
        self
    }

    pub fn defines<K, V>(mut self, defines: impl IntoIterator<Item = (K, V)>) -> Self
    where
        K: AsRef<str>,
        V: AsRef<str>,
    {
        for (key, value) in defines {
            self.build.define(key.as_ref(), Some(value.as_ref()));
        }

        self
    }

    pub fn compile(self, target: &str) {
        self.build.compile(target);
    }
}
