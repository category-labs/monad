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

#[derive(Debug)]
pub enum MonadCMakeLinkage {
    Static,
    Dynamic,
}

pub struct MonadCMake {
    cmake: cmake::Config,
    linkage: MonadCMakeLinkage,
    with_rpath: bool,

    link_libraries: Vec<&'static str>,
}

impl MonadCMake {
    pub fn new<P>(path: P, linkage: MonadCMakeLinkage) -> Self
    where
        P: AsRef<std::path::Path>,
    {
        let mut cmake = cmake::Config::new(path);

        // Default target arch, applied to every language including the
        // assembler: category/core/keccak_impl.S selects an implementation on
        // __AVX2__ / __AVX512F__ and #errors out if neither is enabled, so the
        // arch must reach the assembler and not just C/C++.
        //
        // The repo's toolchain files cannot supply it on this path: they set
        // CMAKE_<LANG>_FLAGS_INIT, which only seeds a flags variable that is
        // not already set, while this crate always passes -DCMAKE_<LANG>_FLAGS=
        // explicitly and so pre-empts the seeding.
        //
        // This is only a default. It is emitted BEFORE the flags from
        // $CFLAGS / $CXXFLAGS / $ASMFLAGS, and for gcc/clang the last -march
        // wins, so an explicitly configured arch still takes effect -- which is
        // how the Dockerfiles and CI workflows set it (all three, to haswell).
        // Use those variables to build for a different arch.
        const DEFAULT_ARCH: &str = "-march=haswell";
        cmake
            .cflag(DEFAULT_ARCH)
            .cxxflag(DEFAULT_ARCH)
            .asmflag(DEFAULT_ARCH);

        match linkage {
            MonadCMakeLinkage::Static => {}
            MonadCMakeLinkage::Dynamic => {
                cmake.define("BUILD_SHARED_LIBS", "ON");
            }
        }

        Self {
            cmake,
            linkage,
            with_rpath: false,

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

    pub fn with_rpath(mut self) -> Self {
        self.with_rpath = true;
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
            linkage,
            with_rpath,

            link_libraries: libraries,
        } = self;

        let dst = cmake.build_target(target).build();

        println!("cargo:rustc-link-search=native={}/build", dst.display());
        println!(
            "cargo:rustc-link-lib={}={}",
            match linkage {
                MonadCMakeLinkage::Static => "static",
                MonadCMakeLinkage::Dynamic => "dylib",
            },
            target
        );
        println!("cargo:CMAKE_BINARY_DIR={}/build", dst.display());

        if with_rpath {
            println!("cargo:rustc-link-arg=-Wl,-rpath,{}/build", dst.display());
        }

        for link_library in libraries {
            println!("cargo:rustc-link-lib={link_library}");
        }
    }
}
