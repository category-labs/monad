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

//! Persistence roundtrip: seed an RNG, generate deterministic (key, value)
//! pairs, write them to a file-backed triedb, drop the handle, re-open the
//! same path read-only, verify every key reads back identically.

use std::{
    fs, io,
    path::{Path, PathBuf},
    process,
    sync::atomic::{AtomicU64, Ordering},
};

use monad_triedb::{NibblesView, Triedb, TriedbRoHandle, TriedbRwHandle, UpsertEntry};

// Deterministic RNG for test key/value generation.
struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 0x9E3779B97F4A7C15 } else { seed },
        }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.state = x;
        x
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut i = 0;
        while i + 8 <= dest.len() {
            dest[i..i + 8].copy_from_slice(&self.next_u64().to_le_bytes());
            i += 8;
        }
        if i < dest.len() {
            let tail_len = dest.len() - i;
            let tail = self.next_u64().to_le_bytes();
            dest[i..].copy_from_slice(&tail[..tail_len]);
        }
    }
}

fn generate_entries(seed: u64, count: usize) -> Vec<UpsertEntry> {
    let mut rng = XorShift64::new(seed);
    (0..count)
        .map(|_| {
            let mut key = vec![0u8; 32];
            rng.fill_bytes(&mut key);
            let value_len = (rng.next_u64() % 96) as usize + 1;
            let mut value = vec![0u8; value_len];
            rng.fill_bytes(&mut value);
            UpsertEntry {
                key,
                key_nibble_len: 64,
                value,
            }
        })
        .collect()
}

// Unique per-test directory under the system temp dir, removed on drop.
static COUNTER: AtomicU64 = AtomicU64::new(0);

struct TempDir {
    path: PathBuf,
}

impl TempDir {
    fn new(label: &str) -> io::Result<Self> {
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let path =
            std::env::temp_dir().join(format!("monad-triedb-test-{}-{}-{n}", process::id(), label));
        fs::create_dir_all(&path)?;
        Ok(Self { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }

    fn db_file(&self) -> PathBuf {
        self.path.join("db")
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[test]
fn write_then_read_only_roundtrip_on_disk() {
    const SEED: u64 = 0xA55AA55A_DEADBEEF;
    const N: usize = 1024;
    const BLOCK_ID: u64 = 0;

    let tmp = TempDir::new("rw-ro-roundtrip").expect("create temp dir");
    let entries = generate_entries(SEED, N);

    {
        let mut rw = TriedbRwHandle::create(&tmp.db_file(), 64 << 20, 4, false)
            .expect("create must succeed on fresh file");
        rw.upsert(&entries, BLOCK_ID);
        rw.update_finalized_version(BLOCK_ID);
        assert_eq!(rw.latest_finalized_block(), Some(BLOCK_ID));
    } // rw drops, flushing in-memory state to the file.

    let ro = TriedbRoHandle::open(tmp.path(), 64 << 20, false)
        .expect("RO open must succeed on the existing directory");
    assert_eq!(
        ro.latest_finalized_block(),
        Some(BLOCK_ID),
        "finalized version should survive close/reopen"
    );

    for (i, entry) in entries.iter().enumerate() {
        let key = NibblesView::new(&entry.key, entry.key_nibble_len).expect("valid key");
        let value = ro
            .find(key, BLOCK_ID)
            .unwrap_or_else(|| panic!("entry {i} missing from re-opened db"));
        assert_eq!(
            value.bytes(),
            entry.value.as_slice(),
            "entry {i}: value mismatch"
        );
    }
}
