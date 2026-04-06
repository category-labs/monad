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

use std::{env, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=triedb-driver");
    println!("cargo:rerun-if-changed=../../category");
    println!("cargo:rerun-if-env-changed=TRIEDB_TARGET");
    let build_execution_lib =
        env::var("TRIEDB_TARGET").is_ok_and(|target| target == "triedb_driver");
    if build_execution_lib {
        // monad-cxx must set this
        let monad_execution_dir = env::var("DEP_MONAD_EXECUTION_CMAKE_BINARY_DIR").unwrap();

        let target = "triedb_driver";

        let dst = cmake::Config::new("triedb-driver")
            .define("BUILD_SHARED_LIBS", "ON")
            .define("MONAD_EXECUTION_DIR", monad_execution_dir)
            .build_target(target)
            .build();

        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dst.display());
        println!("cargo:rustc-link-search=native={}/build", dst.display());
        println!("cargo:rustc-link-lib=dylib={}", target);
    }

    let bindings = bindgen::Builder::default()
        .header("triedb-driver/include/triedb.h")
        .clang_arg("-I../../../")
        // invalidate on header change
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
