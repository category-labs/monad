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

pub use self::bridge::*;
use crate::{async_read_on_complete, traverse_finished_callback, traverse_value_callback};

#[repr(C)]
pub struct OpaqueContext(());

#[cxx::bridge(namespace = "monad::rust")]
pub mod bridge {
    /// One (key, value) pair to upsert. Owns its buffers so C++ can view
    /// them for the duration of the `triedb_upsert` call.
    pub struct UpsertEntry {
        pub key: Vec<u8>,
        pub key_nibble_len: u8,
        pub value: Vec<u8>,
    }

    #[namespace = "monad"]
    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type bytes32_t = crate::Bytes32;
    }

    #[namespace = "monad::staking"]
    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type Validator = crate::Validator;
    }

    #[namespace = "monad::mpt"]
    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type NodeCursor;
    }

    unsafe extern "C++" {
        include!("monad-triedb/include/ffi.h");

        type TriedbRoInner;
        type TriedbRwInner;

        fn triedb_open(
            dbdirpath: &str,
            node_lru_max_mem: u64,
            disable_mismatching_storage_pool_check: bool,
        ) -> UniquePtr<TriedbRoInner>;

        fn triedb_open_rw_memory(
            node_lru_max_mem: u64,
            file_size_gb: i64,
            compaction: bool,
        ) -> UniquePtr<TriedbRwInner>;

        fn triedb_open_rw(
            dbdirpath: &str,
            append: bool,
            node_lru_max_mem: u64,
            file_size_gb: i64,
            compaction: bool,
        ) -> UniquePtr<TriedbRwInner>;

        fn triedb_poll(inner: Pin<&mut TriedbRoInner>, blocking: bool, count: usize) -> usize;

        #[rust_name = "triedb_ro_latest_proposed_version"]
        fn triedb_latest_proposed_version(inner: &TriedbRoInner) -> u64;
        #[rust_name = "triedb_rw_latest_proposed_version"]
        fn triedb_latest_proposed_version(inner: &TriedbRwInner) -> u64;

        #[rust_name = "triedb_ro_latest_voted_version"]
        fn triedb_latest_voted_version(inner: &TriedbRoInner) -> u64;
        #[rust_name = "triedb_rw_latest_voted_version"]
        fn triedb_latest_voted_version(inner: &TriedbRwInner) -> u64;

        #[rust_name = "triedb_ro_latest_finalized_version"]
        fn triedb_latest_finalized_version(inner: &TriedbRoInner) -> u64;
        #[rust_name = "triedb_rw_latest_finalized_version"]
        fn triedb_latest_finalized_version(inner: &TriedbRwInner) -> u64;

        #[rust_name = "triedb_ro_latest_verified_version"]
        fn triedb_latest_verified_version(inner: &TriedbRoInner) -> u64;
        #[rust_name = "triedb_rw_latest_verified_version"]
        fn triedb_latest_verified_version(inner: &TriedbRwInner) -> u64;

        #[rust_name = "triedb_ro_earliest_version"]
        fn triedb_earliest_version(inner: &TriedbRoInner) -> u64;
        #[rust_name = "triedb_rw_earliest_version"]
        fn triedb_earliest_version(inner: &TriedbRwInner) -> u64;

        #[rust_name = "triedb_ro_latest_version"]
        fn triedb_latest_version(inner: &TriedbRoInner) -> u64;
        #[rust_name = "triedb_rw_latest_version"]
        fn triedb_latest_version(inner: &TriedbRwInner) -> u64;

        /// Returns all-zeros if no proposed block is recorded.
        #[rust_name = "triedb_ro_latest_proposed_block_id"]
        fn triedb_latest_proposed_block_id(inner: &TriedbRoInner) -> bytes32_t;
        #[rust_name = "triedb_rw_latest_proposed_block_id"]
        fn triedb_latest_proposed_block_id(inner: &TriedbRwInner) -> bytes32_t;

        /// Returns all-zeros if no voted block is recorded.
        #[rust_name = "triedb_ro_latest_voted_block_id"]
        fn triedb_latest_voted_block_id(inner: &TriedbRoInner) -> bytes32_t;
        #[rust_name = "triedb_rw_latest_voted_block_id"]
        fn triedb_latest_voted_block_id(inner: &TriedbRwInner) -> bytes32_t;

        #[rust_name = "triedb_ro_find"]
        fn triedb_find(
            inner: &TriedbRoInner,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
        ) -> UniquePtr<NodeCursor>;
        #[rust_name = "triedb_rw_find"]
        fn triedb_find(
            inner: &TriedbRwInner,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
        ) -> UniquePtr<NodeCursor>;

        fn node_cursor_value(cursor: &NodeCursor) -> &[u8];

        unsafe fn triedb_async_read(
            inner: Pin<&mut TriedbRoInner>,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut OpaqueContext,
        );

        unsafe fn triedb_traverse_sync(
            inner: Pin<&mut TriedbRoInner>,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut OpaqueContext,
        ) -> bool;

        unsafe fn triedb_async_traverse(
            inner: Pin<&mut TriedbRoInner>,
            key: &[u8],
            key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut OpaqueContext,
        );

        unsafe fn triedb_async_ranged_get(
            inner: Pin<&mut TriedbRoInner>,
            prefix_key: &[u8],
            prefix_key_len_nibbles: u8,
            min_key: &[u8],
            min_key_len_nibbles: u8,
            max_key: &[u8],
            max_key_len_nibbles: u8,
            block_id: u64,
            ctx: *mut OpaqueContext,
        );

        fn triedb_read_valset(
            inner: Pin<&mut TriedbRoInner>,
            block_num: usize,
            requested_epoch: u64,
            found: &mut bool,
        ) -> Vec<Validator>;

        fn triedb_upsert(inner: Pin<&mut TriedbRwInner>, updates: &[UpsertEntry], block_id: u64);

        fn triedb_clear_root(inner: Pin<&mut TriedbRwInner>);

        fn triedb_load_root(inner: Pin<&mut TriedbRwInner>, version: u64) -> bool;

        fn triedb_update_finalized_version(inner: Pin<&mut TriedbRwInner>, version: u64);

        fn triedb_update_voted_metadata(
            inner: Pin<&mut TriedbRwInner>,
            version: u64,
            block_id: &bytes32_t,
        );

        fn triedb_update_proposed_metadata(
            inner: Pin<&mut TriedbRwInner>,
            version: u64,
            block_id: &bytes32_t,
        );
    }

    // Generates VectorElement for Validator so Vec<Validator> is returnable.
    impl Vec<Validator> {}

    extern "Rust" {
        #[cxx_name = "Context"]
        type OpaqueContext;
        unsafe fn async_read_on_complete(ctx: *mut OpaqueContext, value: &[u8], found: bool);
        unsafe fn traverse_value_callback(ctx: *mut OpaqueContext, key: &[u8], value: &[u8]);
        unsafe fn traverse_finished_callback(ctx: *mut OpaqueContext, completed: bool);
    }
}
