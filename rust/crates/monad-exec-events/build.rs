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
    monad_build::bindgen::MonadBindgen::default()
        .header("wrapper.h")
        .derive_copy()
        .derive_hash(Some(r"monad_exec_.+"))
        .derive_partialeq_eq(Some(r"monad_exec_.+"))
        .allowlist_files([
            "category/core/bytes32.h",
            "category/core/event/event_metadata.h",
            "category/execution/ethereum/core/base_ctypes.h",
            "category/execution/ethereum/core/eth_ctypes.h",
            "category/execution/ethereum/event/exec_event_ctypes.h",
            "category/execution/ethereum/event/exec_iter_help.h",
            "category/execution/monad/core/monad_ctypes.h",
        ])
        .blocklist_types(["monad_exec_record_error", "monad_event_record_error"])
        .no_prepend_enum_name()
        .generate_and_build_static("monad_exec_events__wrap_static_fns");
}
