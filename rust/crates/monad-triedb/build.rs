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

const MONAD_ROOT: &str = "../../..";

/// Include dirs, relative to the monad repo root, mirroring the transitive
/// closure computed by `add_subdirectory(third_party/...)` in the C++ build.
const MONAD_INCLUDE_DIRS: &[&str] = &[
    ".", // for `#include <category/...>`
    "third_party/ankerl",
    "third_party/concurrentqueue",
    "third_party/ethash/include",
    "third_party/evmc/include",
    "third_party/fiber/include",
    "third_party/intx/include",
    "third_party/nlohmann_json/include",
    "third_party/unordered_dense/include",
];

const MONAD_COMPILE_DEFINES: &[(&str, &str)] = &[("MONAD_CXX_CTYPES_USE_EVMC_HPP", "1")];

fn main() {
    println!("cargo:rerun-if-changed=src/ffi.cpp");
    println!("cargo:rerun-if-changed=include/ffi.h");
    println!("cargo:rerun-if-changed={MONAD_ROOT}/category");
    println!("cargo:rerun-if-env-changed=TRIEDB_TARGET");

    if env::var("TRIEDB_TARGET").as_deref() != Ok("triedb_driver") {
        return;
    }

    let manifest_dir =
        PathBuf::from(env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR set by cargo"));
    let monad_root = manifest_dir
        .join(MONAD_ROOT)
        .canonicalize()
        .expect("monad repo root not found at ../../..");

    let mut build = cxx_build::bridge("src/ffi.rs");
    build
        .file("src/ffi.cpp")
        .std("c++23")
        .include(&manifest_dir)
        .flag_if_supported("-Wno-missing-field-initializers")
        .flag_if_supported("-Wno-attributes=clang::no_sanitize");

    for include in MONAD_INCLUDE_DIRS {
        build.include(monad_root.join(include));
    }
    for (key, value) in MONAD_COMPILE_DEFINES {
        build.define(key, Some(*value));
    }

    build.compile("monad_triedb_ffi");

    let monad_execution_dir = env::var("DEP_MONAD_EXECUTION_CMAKE_BINARY_DIR").expect(
        "DEP_MONAD_EXECUTION_CMAKE_BINARY_DIR not set; ensure monad-cxx ran with \
         TRIEDB_TARGET=triedb_driver",
    );
    println!("cargo:rustc-link-arg=-Wl,-rpath,{monad_execution_dir}");
    println!("cargo:rustc-link-search=native={monad_execution_dir}");
    println!("cargo:rustc-link-lib=dylib=monad_execution");
}
