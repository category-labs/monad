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

fn main() {
    println!("cargo:rerun-if-changed=../../../category");
    println!("cargo:rerun-if-env-changed=TRIEDB_TARGET");

    let build_execution_lib =
        std::env::var("TRIEDB_TARGET").is_ok_and(|target| target == "triedb_driver");
    if build_execution_lib {
        let target = "monad_execution";
        let dst = cmake::Config::new("../../../")
            .define("BUILD_SHARED_LIBS", "ON")
            .build_target(target)
            .build();

        println!("cargo:rustc-link-search=native={}/build", dst.display());
        println!("cargo:rustc-link-lib=dylib={}", &target);

        // Tell dependent packages where libmonad_execution.so is
        println!("cargo:CMAKE_BINARY_DIR={}/build", dst.display())
    }
}
