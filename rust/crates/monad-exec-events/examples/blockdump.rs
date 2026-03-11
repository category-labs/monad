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

use clap::{CommandFactory, Parser};
use monad_event_ring::{DecodedEventRing, EventNextResult, EventRingPath};
use monad_exec_events::{
    BlockBuilderError, BlockCommitState, CommitStateBlockBuilder, CommitStateBlockUpdate,
    ExecEventRing, ExecutedBlockBuilder,
};

#[derive(Debug, Parser)]
#[command(name = "monad-exec-events-blockdump", about, long_about = None)]
pub struct Cli {
    #[arg(long)]
    event_ring_path: PathBuf,

    #[arg(long)]
    filter_commit_state: Option<String>,

    #[arg(long, default_value_t = false)]
    json: bool,
}

fn main() {
    let Cli {
        event_ring_path,
        filter_commit_state,
        json,
    } = Cli::parse();

    if json && cfg!(not(feature = "alloy")) {
        Cli::command()
            .error(
                clap::error::ErrorKind::InvalidValue,
                "JSON requires compilation with \"alloy\" feature!",
            )
            .exit();
    }

    let filter_commit_state = filter_commit_state.map(|input| match input.as_str() {
        "proposed" => BlockCommitState::Proposed,
        "voted" => BlockCommitState::Voted,
        "finalized" => BlockCommitState::Finalized,
        "verified" => BlockCommitState::Verified,
        _ => panic!("unknown commit state"),
    });

    let event_ring_path = EventRingPath::resolve(event_ring_path).unwrap();

    let event_ring = ExecEventRing::new(event_ring_path).unwrap();

    let mut event_reader = event_ring.create_reader();

    let mut block_builder = CommitStateBlockBuilder::new(ExecutedBlockBuilder::new(true));

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
            Err(BlockBuilderError::Rejected) => panic!("execution rejected block"),
            Err(BlockBuilderError::PayloadExpired) => panic!("event ring payload expired"),
            Err(BlockBuilderError::ImplicitDrop { .. }) => unreachable!(),
            Ok(CommitStateBlockUpdate {
                block,
                state,
                abandoned: _,
            }) => {
                if let Some(filter_commit_state) = filter_commit_state {
                    if filter_commit_state != state {
                        continue;
                    }
                }

                if json {
                    #[cfg(not(feature = "alloy"))]
                    unreachable!();
                    #[cfg(feature = "alloy")]
                    {
                        let alloy_block = block.to_alloy_rpc();
                        println!("{}", serde_json::to_string(&alloy_block).unwrap());
                    }
                } else {
                    println!("{:?}", block);
                }
            }
        }
    }
}
