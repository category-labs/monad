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

use std::{env, path::PathBuf};

fn main() {
    println!("cargo:rerun-if-changed=../../../");
    println!("cargo:rerun-if-env-changed=TRIEDB_TARGET");

    let has_execution_lib = env::var("TRIEDB_TARGET").is_ok_and(|target| target == "triedb_driver");
    if has_execution_lib {
        println!("cargo:rustc-link-lib=dylib=monad_execution");
    }

    let bindings = bindgen::Builder::default()
        .header("../../../category/statesync/statesync_messages.h")
        .header("../../../category/statesync/statesync_client.h")
        .header("../../../category/statesync/statesync_version.h")
        .clang_arg("-I../../../")
        .clang_arg("-std=c23")
        // invalidate on header change
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}
