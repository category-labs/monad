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

use std::path::PathBuf;

const INCLUDES: [(&str, &[&str]); 1] = [(
    "../../../",
    &[
        "category/core/event/event_iterator_inline.h",
        "category/core/event/event_iterator.h",
        "category/core/event/event_metadata.h",
        "category/core/event/event_ring_util.h",
        "category/core/event/event_ring.h",
    ],
)];

const STATIC_FNS_PATH: &str = "monad_event__wrap_static_fns";

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=../../../category");

    let client_target = "monad_event";
    let client_dst = cmake::Config::new("../../../category/event")
        .build_target(client_target)
        .build();

    println!(
        "cargo:rustc-link-search=native={}/build",
        client_dst.display()
    );
    println!("cargo:rustc-link-lib=static=monad_event");
    println!("cargo:rustc-link-lib=zstd");
    #[cfg(target_os = "linux")]
    println!("cargo:rustc-link-lib=hugetlbfs");
    #[cfg(not(target_os = "linux"))]
    println!("cargo:rustc-link-lib=monad_event_os_compat");

    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());

    let mut builder = bindgen::Builder::default()
        .header("wrapper.h")
        .clang_args(["-x", "c", "-std=c23"])
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .wrap_static_fns(true)
        .wrap_static_fns_path(out_dir.join(STATIC_FNS_PATH))
        .derive_copy(true)
        .derive_debug(true)
        .derive_partialeq(true)
        .derive_eq(true)
        .prepend_enum_name(false)
        .allowlist_recursively(false);

    for (lib_path, lib_files) in INCLUDES {
        builder = builder.clang_arg(format!("-I{lib_path}"));

        for lib_file in lib_files {
            builder = builder.allowlist_file(format!("{lib_path}{lib_file}"));
        }
    }

    let bindings = builder.generate().expect("Unable to generate bindings");

    let bindings_str = bindings
        .to_string()
        .replace(r#"#[doc = "<"#, r#"#[doc = ""#)
        .replace(r#"#[doc = " "#, r#"#[doc = ""#);

    std::fs::write(out_dir.join("bindings.rs"), bindings_str).expect("Couldn't write bindings!");

    cc::Build::new()
        .std("c2x")
        .file(out_dir.join(format!("{STATIC_FNS_PATH}.c")))
        .includes(
            std::iter::once(PathBuf::from(env!("CARGO_MANIFEST_DIR"))).chain(
                INCLUDES
                    .iter()
                    .map(|(include_path, _)| PathBuf::from(include_path)),
            ),
        )
        .compile(STATIC_FNS_PATH);
}
