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

pub struct MonadCMake {
    cmake: cmake::Config,
    link_libraries: Vec<&'static str>,
}

impl MonadCMake {
    pub fn new<P>(path: P) -> Self
    where
        P: AsRef<std::path::Path>,
    {
        Self {
            cmake: cmake::Config::new(path),
            link_libraries: Vec::default(),
        }
    }

    pub fn define<V>(mut self, var: &str, value: V) -> Self
    where
        V: AsRef<std::ffi::OsStr>,
    {
        self.cmake.define(var, value);
        self
    }

    pub fn link_libraries(
        mut self,
        link_libraries: impl IntoIterator<Item = &'static str>,
    ) -> Self {
        self.link_libraries.extend(link_libraries);
        self
    }

    pub fn build(self, target: &'static str) {
        let Self {
            mut cmake,
            link_libraries,
        } = self;

        let dst = cmake.build_target(target).build();

        println!("cargo:CMAKE_BINARY_DIR={}/build", dst.display());

        let archive_names = std::iter::once(target)
            .chain(link_libraries.iter().copied())
            .map(|name| format!("lib{name}.a"))
            .collect::<Vec<_>>();

        let mut archive_dirs = vec![dst.join("build")];
        let mut static_libraries: Vec<String> = Vec::new();

        while let Some(dir) = archive_dirs.pop() {
            let Ok(entries) = std::fs::read_dir(&dir) else {
                continue;
            };

            let (dirs, files): (Vec<_>, Vec<_>) = entries
                .flatten()
                .map(|entry| entry.path())
                .partition(|path| path.is_dir());

            archive_dirs.extend(dirs);

            let archives = files
                .iter()
                .filter_map(|path| path.file_name()?.to_str())
                .filter(|name| archive_names.iter().any(|archive| archive == name))
                .filter_map(|name| name.strip_prefix("lib")?.strip_suffix(".a"))
                .map(str::to_owned)
                .collect::<Vec<_>>();

            if !archives.is_empty() {
                println!("cargo:rustc-link-search=native={}", dir.display());
                static_libraries.extend(archives);
            }
        }

        println!("cargo:rustc-link-lib=static={target}");
        for link_library in link_libraries {
            if static_libraries
                .iter()
                .any(|library| library == link_library)
            {
                println!("cargo:rustc-link-lib=static={link_library}");
            } else {
                println!("cargo:rustc-link-lib={link_library}");
            }
        }
    }
}
