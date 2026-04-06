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

pub(crate) use self::bindings::{
    monad_c_bytes32, triedb, triedb_async_ranged_get, triedb_async_read, triedb_async_traverse,
    triedb_async_traverse_callback,
    triedb_async_traverse_callback_triedb_async_traverse_callback_finished_early,
    triedb_async_traverse_callback_triedb_async_traverse_callback_finished_normally,
    triedb_async_traverse_callback_triedb_async_traverse_callback_value, triedb_close,
    triedb_earliest_finalized_block, triedb_finalize, triedb_free_valset,
    triedb_latest_finalized_block, triedb_latest_proposed_block, triedb_latest_proposed_block_id,
    triedb_latest_verified_block, triedb_latest_voted_block, triedb_latest_voted_block_id,
    triedb_open, triedb_poll, triedb_read, triedb_read_valset, triedb_traverse,
};
pub use self::bindings::{validator_data, validator_set};

#[allow(dead_code, non_camel_case_types, non_upper_case_globals)]
mod bindings {
    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
