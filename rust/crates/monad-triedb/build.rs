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

fn main() {
    println!("cargo:rerun-if-changed=CMakeLists.txt");
    println!("cargo:rerun-if-changed=include/ffi.h");
    println!("cargo:rerun-if-changed=src/ffi.cpp");
    println!("cargo:rerun-if-changed=../../../category");

    if let Some(execution_dir) = monad_build::execution_dir() {
        monad_build::MonadCMake::new(".", monad_build::MonadCMakeLinkage::Dynamic)
            .define("MONAD_EXECUTION_DIR", execution_dir)
            .with_rpath()
            .build("triedb_driver");
    }

    monad_build::bindgen::MonadBindgen::default()
        .header("include/ffi.h")
        .generate();
}
