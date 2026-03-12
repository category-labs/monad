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

use std::{path::PathBuf, time::Duration};

use clap::Parser;
use itertools::Itertools;
use monad_event_ring::{
    BytesDecoder, DecodedEventRing, EventNextResult, EventPayloadResult, EventRing, EventRingPath,
};

#[derive(Debug, Parser)]
#[command(name = "monad-exec-events-hexdump", about, long_about = None)]
pub struct Cli {
    #[arg(long)]
    event_ring_path: PathBuf,

    #[arg(short, long, default_value_t = 32)]
    width: usize,
}

fn main() {
    let Cli {
        event_ring_path,
        width,
    } = Cli::parse();

    let event_ring_path = EventRingPath::resolve(event_ring_path).unwrap();

    let event_ring = EventRing::<BytesDecoder>::new(event_ring_path).unwrap();

    let mut event_reader = event_ring.create_reader();

    loop {
        let event_descriptor = match event_reader.next_descriptor() {
            EventNextResult::Gap => panic!("event ring gapped"),
            EventNextResult::NotReady => {
                std::thread::sleep(Duration::from_millis(1));
                continue;
            }
            EventNextResult::Ready(event_descriptor) => event_descriptor,
        };

        // Note: We should NOT call println inside `try_filter_map_raw` as it is possible the bytes
        // are overwritten and the event is thus "Expired" before the println is complete which
        // would lead to invalid bytes being dumped.
        let (info, hexdump) = match event_descriptor.try_filter_map_raw(|info, bytes| {
            Some((
                info,
                bytes
                    .iter()
                    .map(|byte| format!("{byte:02x?}"))
                    .collect_vec(),
            ))
        }) {
            EventPayloadResult::Expired => panic!("event ring payload expired"),
            EventPayloadResult::Ready(None) => unreachable!(),
            EventPayloadResult::Ready(Some(hexdump)) => hexdump,
        };

        println!(
            "{:08x} {:02x} | {}",
            info.seqno,
            info.event_type,
            hexdump
                .into_iter()
                .chunks(width)
                .into_iter()
                .map(|mut chunk| chunk.join(" "))
                .join("\n               ")
        );
    }
}
