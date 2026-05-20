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

use std::path::PathBuf;

pub struct MonadBindgen {
    builder: bindgen::Builder,
    out_dir: PathBuf,
    repo_root: PathBuf,
}

impl Default for MonadBindgen {
    fn default() -> Self {
        let out_dir =
            PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR environment variable not set"));

        let repo_root = crate::repository_root();
        let include_path = format!("-I{}", repo_root.display());

        let builder = bindgen::Builder::default()
            .parse_callbacks(Box::new(::bindgen::CargoCallbacks::new()))
            .clang_args(["-x", "c", "-std=c23", &include_path])
            .prepend_enum_name(true)
            .allowlist_recursively(true)
            .derive_debug(true);

        Self {
            builder,
            out_dir,
            repo_root,
        }
    }
}

impl MonadBindgen {
    pub fn header(mut self, header: &str) -> Self {
        self.builder = self.builder.header(header);
        self
    }

    pub fn derive_copy(mut self) -> Self {
        self.builder = self.builder.derive_copy(true);
        self
    }

    pub fn derive_hash(mut self, except: Option<&'static str>) -> Self {
        self.builder = self.builder.derive_hash(true);
        if let Some(pattern) = except {
            self.builder = self.builder.no_hash(pattern);
        }
        self
    }

    pub fn derive_partialeq_eq(mut self, except: Option<&'static str>) -> Self {
        self.builder = self.builder.derive_partialeq(true).derive_eq(true);

        if let Some(pattern) = except {
            self.builder = self.builder.no_partialeq(pattern);
        }

        self
    }

    pub fn allowlist_files<S>(mut self, files: impl IntoIterator<Item = S>) -> Self
    where
        S: AsRef<str>,
    {
        self.builder = self.builder.allowlist_recursively(false);

        for file in files {
            let file_ref = file.as_ref();

            let file_path = self.repo_root.join(file_ref);
            assert!(
                file_path.exists(),
                "allowlist_files: {} not found at {}",
                file_ref,
                file_path.display()
            );

            self.builder = self.builder.allowlist_file(file_path.to_string_lossy());
        }

        self
    }

    pub fn blocklist_types<S>(mut self, types: impl IntoIterator<Item = S>) -> Self
    where
        S: AsRef<str>,
    {
        for ty in types {
            self.builder = self.builder.blocklist_type(ty.as_ref());
        }

        self
    }

    pub fn no_prepend_enum_name(mut self) -> Self {
        self.builder = self.builder.prepend_enum_name(false);
        self
    }

    pub fn generate(self) {
        let Self {
            builder,
            out_dir,
            repo_root: _,
        } = self;

        let bindings = builder.generate().expect("Unable to generate bindings");

        let bindings_str = bindings
            .to_string()
            .replace(r#"#[doc = "<"#, r#"#[doc = ""#)
            .replace(r#"#[doc = " "#, r#"#[doc = ""#);

        std::fs::write(out_dir.join("bindings.rs"), bindings_str)
            .expect("Failed to write bindings.rs");
    }

    #[cfg(feature = "bindgen-static")]
    pub fn generate_and_build_static(mut self, static_file_name: &'static str) {
        self.builder = self
            .builder
            .wrap_static_fns(true)
            .wrap_static_fns_path(self.out_dir.join(static_file_name));

        let mut cc_build = cc::Build::new();
        cc_build
            .std("c2x")
            .include(std::env::var("CARGO_MANIFEST_DIR").unwrap())
            .include(&self.repo_root)
            .file(self.out_dir.join(format!("{}.c", static_file_name)));

        self.generate();

        cc_build.compile(static_file_name);
    }
}
