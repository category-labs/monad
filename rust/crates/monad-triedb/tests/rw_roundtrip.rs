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

//! Integration tests exercising the in-memory read-write path.
//!
//! These tests only run when the C++ library is actually linked in, which
//! requires building with `TRIEDB_TARGET=triedb_driver`. Without that,
//! the test binary would fail to link; we gate with a cfg check so
//! `cargo check` remains fast.

use monad_triedb::{NibblesView, Triedb, TriedbRwHandle, UpsertEntry};

fn sample_entries(count: usize) -> Vec<UpsertEntry> {
    (0..count)
        .map(|i| {
            // 32-byte key encoding i in big-endian; each key is unique.
            let mut key = vec![0u8; 32];
            key[24..].copy_from_slice(&(i as u64).to_be_bytes());
            let value = format!("value-{i}").into_bytes();
            UpsertEntry {
                key,
                key_nibble_len: 64,
                value,
            }
        })
        .collect()
}

#[test]
fn open_rw_memory_and_find_returns_inserted_values() {
    let mut db =
        TriedbRwHandle::open_rw_memory(64 << 20, 4, false).expect("open_rw_memory must succeed");

    let entries = sample_entries(16);
    db.upsert(&entries, 0);
    db.update_finalized_version(0);

    for entry in &entries {
        let key = NibblesView::new(&entry.key, entry.key_nibble_len).expect("key should be valid");
        let value = db
            .find(key, 0)
            .expect("key should be present")
            .into_boxed_slice();
        assert_eq!(value.as_ref(), entry.value.as_slice());
    }
}

#[test]
fn missing_key_returns_none() {
    let db =
        TriedbRwHandle::open_rw_memory(64 << 20, 4, false).expect("open_rw_memory must succeed");

    let key_bytes = [0u8; 32];
    let key = NibblesView::new(&key_bytes, 64).unwrap();
    assert!(db.find(key, 0).is_none());
}

#[test]
fn block_version_metadata_updates() {
    let mut db =
        TriedbRwHandle::open_rw_memory(64 << 20, 4, false).expect("open_rw_memory must succeed");

    db.upsert(&sample_entries(4), 0);
    db.update_finalized_version(0);

    assert_eq!(db.latest_finalized_block(), Some(0));
    assert_eq!(db.earliest_finalized_block(), Some(0));
}

#[test]
fn rw_handle_is_also_a_reader() {
    fn _asserts_rw_can_read(h: &TriedbRwHandle) -> Option<u64> {
        h.latest_finalized_block()
    }
}
