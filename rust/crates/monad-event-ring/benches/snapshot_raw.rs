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

use std::hint::black_box;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use monad_event_ring::{
    BytesDecoder, DecodedEventRing, EventNextResult, EventPayloadResult, SnapshotEventRing,
};

fn bench_snapshot(c: &mut Criterion) {
    const SNAPSHOT_NAME: &str = "ETHEREUM_MAINNET_30B_15M";
    const SNAPSHOT_ZSTD_BYTES: &[u8] =
        include_bytes!("../../monad-exec-events/test/data/exec-events-emn-30b-15m/snapshot.zst");

    let mut g = c.benchmark_group("snapshot_raw");

    let snapshot =
        SnapshotEventRing::<BytesDecoder>::new_from_zstd_bytes(SNAPSHOT_ZSTD_BYTES, SNAPSHOT_NAME)
            .unwrap();

    let items = {
        let mut event_reader = snapshot.create_reader();

        let mut items = 0;

        loop {
            match event_reader.next_descriptor() {
                EventNextResult::Ready(_) => {
                    items += 1;
                }
                EventNextResult::NotReady => break,
                EventNextResult::Gap => panic!("snapshot cannot gap"),
            }
        }

        items
    };

    g.bench_function("reader_create_drop", |b| {
        b.iter(|| {
            black_box(snapshot.create_reader());
        });
    });

    g.throughput(criterion::Throughput::Elements(items));
    g.bench_function("iter", |b| {
        b.iter_batched_ref(
            || snapshot.create_reader(),
            |event_reader| loop {
                match event_reader.next_descriptor() {
                    EventNextResult::Ready(event_descriptor) => {
                        let actual_payload: EventPayloadResult<Option<u8>> = event_descriptor
                            .try_filter_map_raw(|_, bytes| {
                                black_box(Some(bytes.first().cloned().unwrap_or_default()))
                            });

                        black_box(actual_payload);
                    }
                    EventNextResult::NotReady => break,
                    EventNextResult::Gap => panic!("snapshot cannot gap"),
                };
            },
            BatchSize::SmallInput,
        );
    });
}

criterion_group!(benches, bench_snapshot);
criterion_main!(benches);
