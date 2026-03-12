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
use monad_event_ring::{DecodedEventRing, EventNextResult, EventRingPath};
use monad_exec_events::{BlockBuilderError, ExecEventRing, ExecutedBlockBuilder};

#[derive(Debug, Parser)]
#[command(name = "monad-exec-events-blockdump-simple", about, long_about = None)]
pub struct Cli {
    #[arg(long)]
    event_ring_path: PathBuf,
}

fn main() {
    let Cli { event_ring_path } = Cli::parse();

    let event_ring_path = EventRingPath::resolve(event_ring_path).unwrap();

    let event_ring = ExecEventRing::new(event_ring_path).unwrap();

    let mut event_reader = event_ring.create_reader();

    let mut block_builder = ExecutedBlockBuilder::new(true);

    loop {
        let event = match event_reader.next_descriptor() {
            EventNextResult::Gap => panic!("event ring gapped"),
            EventNextResult::NotReady => {
                std::thread::sleep(Duration::from_millis(1));
                continue;
            }
            EventNextResult::Ready(event) => event,
        };

        let Some(result) = block_builder.process_event_descriptor(&event) else {
            continue;
        };

        match result {
            Err(BlockBuilderError::Rejected) => unreachable!(),
            Err(BlockBuilderError::PayloadExpired) => panic!("event ring payload expired"),
            Err(BlockBuilderError::ImplicitDrop { .. }) => unreachable!(),
            Ok(executed_block) => {
                println!("{executed_block:?}");
            }
        }
    }
}
