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
    let mut link_libs = vec!["zstd"];
    if build_rs::input::cargo_cfg_target_os() != "linux" {
        link_libs.push("monad_event_os_compat");
    }

    monad_build::MonadCMake::new(
        monad_build::repository_root().join("category/event"),
        monad_build::MonadCMakeLinkage::Static,
    )
    .link_libraries(link_libs)
    .build("monad_event");

    monad_build::bindgen::MonadBindgen::default()
        .header("wrapper.h")
        .derive_copy()
        .derive_partialeq_eq(None)
        .allowlist_files([
            "category/core/event/event_iterator_inline.h",
            "category/core/event/event_iterator.h",
            "category/core/event/event_metadata.h",
            "category/core/event/event_ring_util.h",
            "category/core/event/event_ring.h",
        ])
        .no_prepend_enum_name()
        .generate_and_build_static("monad_event__wrap_static_fns");
}
