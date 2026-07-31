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
    if monad_build::should_build_execution() {
        let root = monad_build::repository_root();
        for path in ["CMakeLists.txt", "cmake", "category", "third_party"] {
            println!("cargo:rerun-if-changed={}", root.join(path).display());
        }
        monad_build::MonadCMake::new(&root, monad_build::MonadCMakeLinkage::Dynamic)
            .build("monad_execution");
    }

    monad_build::bindgen::MonadBindgen::default()
        .header("wrapper.h")
        .derive_copy()
        .allowlist_files(["category/core/log_ffi.h"])
        .generate();
}
