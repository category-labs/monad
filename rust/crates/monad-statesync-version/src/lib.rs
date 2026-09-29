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

//! The statesync protocol version numbers, generated from execution's
//! `category/statesync/statesync_version.h`. Split out from `monad-statesync`
//! so that consumers of the constants alone -- monad-bft's message types --
//! need neither the C++ library nor a libc, and so stay buildable for wasm.

pub use self::bindings::{
    monad_statesync_protocol_version_MONAD_STATESYNC_VERSION as MONAD_STATESYNC_VERSION,
    monad_statesync_protocol_version_MONAD_STATESYNC_VERSION_MIN as MONAD_STATESYNC_VERSION_MIN,
    monad_statesync_version_num_MONAD_STATESYNC_MAJOR as MONAD_STATESYNC_MAJOR,
    monad_statesync_version_num_MONAD_STATESYNC_MINOR_2 as MONAD_STATESYNC_MINOR_2,
    monad_statesync_version_num_MONAD_STATESYNC_MINOR_3 as MONAD_STATESYNC_MINOR_3,
};

#[allow(dead_code, non_camel_case_types, non_upper_case_globals)]
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
