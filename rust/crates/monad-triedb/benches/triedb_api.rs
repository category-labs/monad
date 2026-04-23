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

//! Benchmarks for the public API of `monad-triedb`.
//!
//! Requires a populated DB at `./test_db/`. Generate it with
//! `scripts/populate-1m.sh`. The bench assumes:
//!   - Keys are 8 bytes (16 nibbles), big-endian u64 in 1..=1048576.
//!   - Values are 16 bytes: the key bytes repeated twice.
//!   - Latest finalized block is 1024.
//!
//! Key selection for read benches is driven by a seeded `StdRng` so runs
//! are reproducible. Each returned value is compared against the
//! fixture's expected `value = key || key` invariant.

use std::{hint::black_box, path::Path};

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use futures::channel::oneshot;
use monad_triedb::{NibblesView, Triedb, TriedbRoHandle};
use rand::{rngs::StdRng, Rng, SeedableRng};

const DB_PATH: &str = "./test_db";
const NODE_LRU_MAX_MEM: u64 = 256 << 20;
const TOTAL_KEYS: u64 = 1024 * 1024;
const READ_BLOCK_ID: u64 = 1024;

const READ_PRESENT_SEED: u64 = 0xA11CE_C0FFEE_01;
const READ_ABSENT_SEED: u64 = 0xA11CE_C0FFEE_02;
const READ_ASYNC_SINGLE_SEED: u64 = 0xA11CE_C0FFEE_03;
const READ_ASYNC_BATCH_SEED: u64 = 0xA11CE_C0FFEE_04;

fn encode_key(index: u64) -> [u8; 8] {
    index.to_be_bytes()
}

/// The fixture stores `value = key || key` for every populated key.
fn expected_value(index: u64) -> [u8; 16] {
    let key = encode_key(index);
    let mut value = [0u8; 16];
    value[..8].copy_from_slice(&key);
    value[8..].copy_from_slice(&key);
    value
}

fn assert_entry_invariant(prefix_bytes: &[u8], relative_key: &[u8], value: &[u8]) {
    let mut full_key = Vec::with_capacity(prefix_bytes.len() + relative_key.len());
    full_key.extend_from_slice(prefix_bytes);
    full_key.extend_from_slice(relative_key);

    assert_eq!(
        full_key.len(),
        8,
        "unexpected full key length {}",
        full_key.len()
    );
    assert_eq!(value.len(), 16, "unexpected value length {}", value.len());
    assert_eq!(
        &value[..8],
        full_key.as_slice(),
        "value first half must equal full key"
    );
    assert_eq!(
        &value[8..],
        full_key.as_slice(),
        "value second half must equal full key"
    );
}

fn open_handle() -> TriedbRoHandle {
    TriedbRoHandle::open(Path::new(DB_PATH), NODE_LRU_MAX_MEM, false).unwrap_or_else(|e| {
        panic!(
            "failed to open triedb at {DB_PATH}: {e}; populate it with \
             `scripts/populate-1m.sh` from the monad-triedb crate root"
        )
    })
}

fn bench_find(c: &mut Criterion) {
    let handle = open_handle();

    let mut group = c.benchmark_group("read");
    group.throughput(Throughput::Elements(1));

    group.bench_function("present_key", |b| {
        let mut rng = StdRng::seed_from_u64(READ_PRESENT_SEED);
        b.iter(|| {
            let index = rng.random_range(1..=TOTAL_KEYS);
            let key_bytes = encode_key(index);
            let key = NibblesView::from_bytes(&key_bytes).expect("key fits in u8 nibbles");
            let node = handle
                .find(key, READ_BLOCK_ID)
                .expect("populated key must be present");
            assert_eq!(node.bytes(), expected_value(index));
            black_box(node);
        });
    });

    group.bench_function("absent_key", |b| {
        let mut rng = StdRng::seed_from_u64(READ_ABSENT_SEED);
        b.iter(|| {
            let index = rng.random_range((TOTAL_KEYS + 1)..=(2 * TOTAL_KEYS));
            let key_bytes = encode_key(index);
            let key = NibblesView::from_bytes(&key_bytes).expect("key fits in u8 nibbles");
            let result = handle.find(key, READ_BLOCK_ID);
            assert!(result.is_none(), "absent key must not be found");
            black_box(result);
        });
    });

    group.finish();
}

fn bench_find_async_single(c: &mut Criterion) {
    let mut handle = open_handle();

    let mut group = c.benchmark_group("read_async_single");
    group.throughput(Throughput::Elements(1));

    group.bench_function("present_key", |b| {
        let mut rng = StdRng::seed_from_u64(READ_ASYNC_SINGLE_SEED);
        b.iter(|| {
            let index = rng.random_range(1..=TOTAL_KEYS);
            let key_bytes = encode_key(index);
            let key = NibblesView::from_bytes(&key_bytes).expect("key fits in u8 nibbles");

            let (tx, mut rx) = oneshot::channel::<Option<Box<[u8]>>>();
            handle.find_async(key, READ_BLOCK_ID, tx);

            let value = loop {
                match rx.try_recv() {
                    Ok(Some(result)) => break result.expect("key must be present"),
                    Ok(None) => {
                        handle.poll(true, 1);
                    }
                    Err(_) => panic!("sender dropped"),
                }
            };
            assert_eq!(&*value, &expected_value(index));
            black_box(value);
        });
    });

    group.finish();
}

fn bench_find_async_batch(c: &mut Criterion) {
    let mut handle = open_handle();

    let mut group = c.benchmark_group("read_async_batch");

    const BATCH_SIZES: &[usize] = &[1, 16, 64, 256, 1024];

    for &batch_size in BATCH_SIZES {
        group.throughput(Throughput::Elements(batch_size as u64));
        group.bench_with_input(
            BenchmarkId::from_parameter(batch_size),
            &batch_size,
            |b, &batch_size| {
                let mut rng = StdRng::seed_from_u64(READ_ASYNC_BATCH_SEED);
                b.iter(|| {
                    let mut pending: Vec<(u64, oneshot::Receiver<Option<Box<[u8]>>>)> =
                        Vec::with_capacity(batch_size);
                    for _ in 0..batch_size {
                        let index = rng.random_range(1..=TOTAL_KEYS);
                        let key_bytes = encode_key(index);
                        let key =
                            NibblesView::from_bytes(&key_bytes).expect("key fits in u8 nibbles");

                        let (tx, rx) = oneshot::channel();
                        handle.find_async(key, READ_BLOCK_ID, tx);
                        pending.push((index, rx));
                    }

                    let mut remaining = batch_size;
                    let mut results: Vec<Option<Box<[u8]>>> = vec![None; batch_size];
                    while remaining > 0 {
                        let mut progressed = false;
                        for (i, (_index, rx)) in pending.iter_mut().enumerate() {
                            if results[i].is_some() {
                                continue;
                            }
                            if let Ok(Some(result)) = rx.try_recv() {
                                results[i] = Some(result.expect("key must be present"));
                                remaining -= 1;
                                progressed = true;
                            }
                        }
                        if remaining > 0 && !progressed {
                            handle.poll(true, remaining);
                        }
                    }

                    for ((index, _), maybe_value) in pending.iter().zip(results.iter()) {
                        let value = maybe_value.as_ref().expect("all results populated");
                        assert_eq!(&**value, &expected_value(*index));
                        black_box(value);
                    }
                });
            },
        );
    }

    group.finish();
}

// Traverse prefix for bench_traverse. prefix_nibbles=14 reads only the
// first 7 bytes of the buffer; the 8th is ignored. The chosen prefix
// `00 00 00 00 00 00 01` matches keys where byte[6] == 0x01 and byte[7]
// varies over 0x00..0xFF, i.e. fixture indices 256..=511 (256 keys, all
// populated).
const TRAVERSE_PREFIX: &[u8] = &[0, 0, 0, 0, 0, 0, 0x01, 0x00];
const TRAVERSE_PREFIX_NIBBLES: u8 = 14;
const TRAVERSE_EXPECTED_LEAVES: u64 = 256;

fn bench_traverse_async(c: &mut Criterion) {
    let mut handle = open_handle();
    let mut group = c.benchmark_group("traverse_async");
    group.throughput(Throughput::Elements(TRAVERSE_EXPECTED_LEAVES));

    group.bench_function("subtrie", |b| {
        b.iter(|| {
            let prefix =
                NibblesView::new(TRAVERSE_PREFIX, TRAVERSE_PREFIX_NIBBLES).expect("prefix fits");

            let (tx, mut rx) = oneshot::channel();
            handle.traverse(prefix, READ_BLOCK_ID, tx);

            let entries = loop {
                match rx.try_recv() {
                    Ok(Some(result)) => break result.expect("traverse completed"),
                    Ok(None) => {
                        handle.poll(true, 64);
                    }
                    Err(_) => panic!("sender dropped"),
                }
            };

            assert_eq!(entries.len() as u64, TRAVERSE_EXPECTED_LEAVES);
            let prefix_bytes = &TRAVERSE_PREFIX[..TRAVERSE_PREFIX_NIBBLES as usize / 2];
            for entry in &entries {
                assert_entry_invariant(prefix_bytes, &entry.key, &entry.value);
            }
            black_box(entries);
        });
    });

    group.finish();
}

fn bench_traverse_range(c: &mut Criterion) {
    let mut handle = open_handle();
    let mut group = c.benchmark_group("range_get_async");

    // Keys in [0x1000, 0x1100) = 256 keys.
    let min_bytes: [u8; 8] = 0x1000u64.to_be_bytes();
    let max_bytes: [u8; 8] = 0x1100u64.to_be_bytes();
    const EXPECTED: u64 = 0x100;

    group.throughput(Throughput::Elements(EXPECTED));
    group.bench_function("256_keys", |b| {
        b.iter(|| {
            let prefix = NibblesView::empty();
            let min = NibblesView::from_bytes(&min_bytes).expect("min fits");
            let max = NibblesView::from_bytes(&max_bytes).expect("max fits");

            let (tx, mut rx) = oneshot::channel();
            handle.traverse_range(prefix, min, max, READ_BLOCK_ID, tx);

            let entries = loop {
                match rx.try_recv() {
                    Ok(Some(result)) => break result.expect("range traverse completed"),
                    Ok(None) => {
                        handle.poll(true, 64);
                    }
                    Err(_) => panic!("sender dropped"),
                }
            };

            assert_eq!(entries.len() as u64, EXPECTED);
            for entry in &entries {
                assert_entry_invariant(&[], &entry.key, &entry.value);
            }
            black_box(entries);
        });
    });

    group.finish();
}

fn bench_metadata(c: &mut Criterion) {
    let handle = open_handle();
    let mut group = c.benchmark_group("metadata");

    group.bench_function("latest_finalized_block", |b| {
        b.iter(|| black_box(handle.latest_finalized_block()));
    });
    group.bench_function("latest_verified_block", |b| {
        b.iter(|| black_box(handle.latest_verified_block()));
    });
    group.bench_function("latest_proposed_block", |b| {
        b.iter(|| black_box(handle.latest_proposed_block()));
    });
    group.bench_function("latest_voted_block", |b| {
        b.iter(|| black_box(handle.latest_voted_block()));
    });
    group.bench_function("earliest_finalized_block", |b| {
        b.iter(|| black_box(handle.earliest_finalized_block()));
    });
    group.bench_function("latest_proposed_block_id", |b| {
        b.iter(|| black_box(handle.latest_proposed_block_id()));
    });
    group.bench_function("latest_voted_block_id", |b| {
        b.iter(|| black_box(handle.latest_voted_block_id()));
    });

    group.finish();
}

fn bench_open_close(c: &mut Criterion) {
    let mut group = c.benchmark_group("open_close");
    group.sample_size(10);

    group.bench_function("try_new_then_drop", |b| {
        b.iter(|| {
            let handle = TriedbRoHandle::open(Path::new(DB_PATH), NODE_LRU_MAX_MEM, false)
                .expect("open must succeed for bench");
            black_box(&handle);
            drop(handle);
        });
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_find,
    bench_find_async_single,
    bench_find_async_batch,
    bench_traverse_async,
    bench_traverse_range,
    bench_metadata,
    bench_open_close,
);
criterion_main!(benches);
