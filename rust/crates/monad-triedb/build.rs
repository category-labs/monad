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

use std::path::PathBuf;

fn main() {
    let Some(execution_dir) = monad_build::execution_dir() else {
        return;
    };

    monad_build::MonadCxx::new("src/ffi.rs")
        .file("src/ffi.cpp")
        .defines([
            ("MONAD_CXX_CTYPES_USE_EVMC_HPP", "1"),
            ("QUILL_ROOT_LOGGER_ONLY", "1"),
        ])
        .includes([
            "third_party/ankerl",
            "third_party/concurrentqueue",
            "third_party/ethash/include",
            "third_party/evmc/include",
            "third_party/fiber/include",
            "third_party/intx/include",
            "third_party/nlohmann_json/include",
            "third_party/quill/quill/include",
            "third_party/unordered_dense/include",
        ])
        .compile("monad_triedb_ffi");

    // TODO(andr-dev): Remove this special casing after migrating to non-execution dependent build
    println!(
        "cargo::rustc-link-search=native={}",
        PathBuf::from(execution_dir)
            .join("third_party/quill/quill")
            .display()
    );
    println!("cargo::rustc-link-lib=quill");
}
