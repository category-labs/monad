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

use std::{
    collections::{hash_map::Entry as HashMapEntry, BTreeMap, HashMap, HashSet},
    sync::Arc,
};

use monad_event_ring::{EventDescriptor, EventPayloadResult};
use serde::{Deserialize, Serialize};
use tracing::{debug, error};

use super::BlockBuilderError;
use crate::{
    block_builder::{BlockBuilderResult, ExecutedBlockBuilder},
    ffi::monad_c_bytes32,
    ExecEvent, ExecEventDecoder, ExecEventRef, ExecutedBlock,
};

/// Represents the different block commit states from MonadBFT.
///
/// See
/// [block states](<https://docs.monad.xyz/monad-arch/consensus/asynchronous-execution#block-states>)
/// for more details.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BlockCommitState {
    /// The block has been proposed by a leader but has not been voted upon.
    Proposed,
    /// The block has been voted on affirmatively by a supermajority.
    Voted,
    /// The next block has been voted on affirmatively by a supermajority leading to finality of the current block.
    Finalized,
    /// The block's execution outputs and state root have been included in a finalized block.
    Verified,
}

/// Represents a change in a block's commit state.
#[derive(Debug)]
pub struct CommitStateBlockUpdate {
    /// The block whose commit state changed.
    pub block: Arc<ExecutedBlock>,
    /// The new commit state.
    pub state: BlockCommitState,
    /// Blocks that were abandoned as a result of the block commit change.
    pub abandoned: Vec<Arc<ExecutedBlock>>,
}

/// Produces block commit state notifications for an execution event ring.
#[derive(Debug)]
pub struct CommitStateBlockBuilder {
    state: HashMap<monad_c_bytes32, (Arc<ExecutedBlock>, BlockCommitState)>,
    proposals: BTreeMap<u64, HashSet<monad_c_bytes32>>,

    block_builder: ExecutedBlockBuilder,
}

impl CommitStateBlockBuilder {
    /// Creates a new [`CommitStateBlockBuilder`] using the provided [`ExecutedBlockBuilder`] as the
    /// underlying block builder.
    pub fn new(block_builder: ExecutedBlockBuilder) -> Self {
        Self {
            state: HashMap::default(),
            proposals: BTreeMap::default(),
            block_builder,
        }
    }

    /// Processes the execution event in the provided event descriptor.
    pub fn process_event_descriptor(
        &mut self,
        event_descriptor: &EventDescriptor<'_, ExecEventDecoder>,
    ) -> Option<BlockBuilderResult<CommitStateBlockUpdate>> {
        match event_descriptor.try_filter_map(Self::select_commit_state_event_refs) {
            EventPayloadResult::Ready(Some(exec_event)) => {
                self.process_commit_state_event(exec_event).map(Ok)
            }
            EventPayloadResult::Ready(None) => {
                // CommitStateBlockBuilder and ExecutedBlockBuilder select mutually exclusive
                // events. If the event in the event descriptor does not correspond to the
                // CommitStateBlockBuilder, we allow the ExecutedBlockBuilder to process it.
                self.block_builder
                    .process_event_descriptor(event_descriptor)
                    .map(|result| self.process_block_builder_result(result))
            }
            EventPayloadResult::Expired => {
                self.reset();

                Some(Err(BlockBuilderError::PayloadExpired))
            }
        }
    }

    fn process_block_builder_result(
        &mut self,
        result: BlockBuilderResult<ExecutedBlock>,
    ) -> BlockBuilderResult<CommitStateBlockUpdate> {
        result.map(|executed_block| {
            let block_id = executed_block.start.block_tag.id;

            match self.state.entry(block_id) {
                HashMapEntry::Occupied(occupied_entry) => {
                    panic!(
                        "CommitStateBlockBuilder produced executed block {:x?} twice",
                        occupied_entry.key()
                    );
                }
                HashMapEntry::Vacant(v) => {
                    let executed_block = Arc::new(executed_block);

                    v.insert((executed_block.clone(), BlockCommitState::Proposed));

                    if !self
                        .proposals
                        .entry(executed_block.start.block_tag.block_number)
                        .or_default()
                        .insert(block_id)
                    {
                        panic!("CommitStateBlockBuilder received block already in proposals");
                    }

                    CommitStateBlockUpdate {
                        block: executed_block,
                        state: BlockCommitState::Proposed,
                        abandoned: vec![],
                    }
                }
            }
        })
    }

    fn select_commit_state_event_refs(event_ref: ExecEventRef<'_>) -> Option<ExecEvent> {
        match event_ref {
            event @ (ExecEventRef::BlockQC(_)
            | ExecEventRef::BlockFinalized(_)
            | ExecEventRef::BlockVerified(_)) => Some(event.into_owned()),
            _ => None,
        }
    }

    fn process_commit_state_event(
        &mut self,
        exec_event: ExecEvent,
    ) -> Option<CommitStateBlockUpdate> {
        match exec_event {
            ExecEvent::BlockQC(block_qc) => {
                let Some((executed_block, state)) = self.state.get_mut(&block_qc.block_tag.id)
                else {
                    assert!(
                        self.proposals
                            .get(&block_qc.block_tag.block_number)
                            .is_none_or(|candidates| !candidates.contains(&block_qc.block_tag.id)),
                        "CommitStateBlockBuilder received qc for block in proposals but not in state"
                    );
                    return None;
                };

                match state {
                    BlockCommitState::Proposed => {}
                    BlockCommitState::Voted => {
                        debug!("CommitStateBlockBuilder received another QC commit state update for voted proposal");
                        return None;
                    }
                    BlockCommitState::Finalized | BlockCommitState::Verified => {
                        error!(?state, "CommitStateBlockBuilder received QC commit state update for finalized proposal id");
                        return None;
                    }
                }
                *state = BlockCommitState::Voted;

                Some(CommitStateBlockUpdate {
                    block: executed_block.clone(),
                    state: *state,
                    abandoned: vec![],
                })
            }
            ExecEvent::BlockFinalized(block_tag) => {
                let Some((executed_block, state)) = self.state.get_mut(&block_tag.id) else {
                    assert!(
                        self.proposals
                            .get(&block_tag.block_number)
                            .is_none_or(|candidates| !candidates.contains(&block_tag.id)),
                        "CommitStateBlockBuilder received finalized for block in proposals but not in state"
                    );
                    return None;
                };

                match state {
                    BlockCommitState::Proposed | BlockCommitState::Voted => {}
                    BlockCommitState::Finalized | BlockCommitState::Verified => {
                        panic!("CommitStateBlockBuilder received finalized proposal id for already-finalized proposal");
                    }
                }
                *state = BlockCommitState::Finalized;

                let (block, state) = (executed_block.clone(), *state);

                let candidates = self
                    .proposals
                    .get_mut(&block_tag.block_number)
                    .expect("CommitStateBlockBuilder added finalized block to state and proposals");
                assert!(candidates.contains(&block_tag.id),
                 "CommitStateBlockBuilder received finalized for block in state but not in candidates");

                let abandoned = candidates
                    .drain()
                    .filter(|block_id| block_id != &block_tag.id)
                    .map(|abandoned| {
                        self.state
                            .remove(&abandoned)
                            .expect("CommitStateBlockBuilder added block to proposals and state")
                            .0
                    })
                    .collect::<Vec<_>>();

                candidates.insert(block_tag.id);

                Some(CommitStateBlockUpdate {
                    block,
                    state,
                    abandoned,
                })
            }
            ExecEvent::BlockVerified(block_verified) => {
                let proposals = self.proposals.remove(&block_verified.block_number)?;

                if let Some((lowest_block_number, _)) = self.proposals.first_key_value() {
                    assert!(
                        lowest_block_number > &block_verified.block_number,
                        "CommitStateBlockBuilder received gapped verified block number"
                    );
                }

                let mut proposals = proposals.into_iter();

                let proposal = proposals.next().expect(
                    "CommitStateBlockBuilder verified block number has at least one proposal",
                );

                assert!(
                    proposals.next().is_none(),
                    "CommitStateBlockBuilder verified block number has no more than one proposal"
                );

                let (block, state) = self
                    .state
                    .remove(&proposal)
                    .expect("CommitStateBlockBuilder added proposal to proposals and state");

                if state != BlockCommitState::Finalized {
                    error!(?state, "CommitStateBlockBuilder received verified block number for non-finalized proposal");
                }

                Some(CommitStateBlockUpdate {
                    block,
                    state: BlockCommitState::Verified,
                    abandoned: vec![],
                })
            }
            _ => unreachable!(),
        }
    }

    /// Resets the state of the commit state block builder.
    ///
    /// <div class="warning">
    ///
    /// See [`ExecutedBlockBuilder::reset`] for more details.
    ///
    /// </div>
    pub fn reset(&mut self) {
        self.state.clear();
        self.proposals.clear();

        self.block_builder.reset();
    }
}

#[cfg(test)]
mod test {
    use monad_event_ring::{DecodedEventRing, EventNextResult};

    use super::CommitStateBlockBuilder;
    use crate::{
        BlockBuilderError, CommitStateBlockUpdate, ExecSnapshotEventRing, ExecutedBlockBuilder,
    };

    fn run_commit_state_block_builder(
        snapshot_name: &'static str,
        snapshot_zstd_bytes: &'static [u8],
    ) {
        let snapshot =
            ExecSnapshotEventRing::new_from_zstd_bytes(snapshot_name, snapshot_zstd_bytes, None)
                .unwrap();

        let mut event_reader = snapshot.create_reader();

        let mut block_builder = CommitStateBlockBuilder::new(ExecutedBlockBuilder::new(true));

        loop {
            let event_descriptor = match event_reader.next_descriptor() {
                EventNextResult::NotReady => break,
                EventNextResult::Gap => panic!("snapshot cannot gap"),
                EventNextResult::Ready(event_descriptor) => event_descriptor,
            };

            let Some(result) = block_builder.process_event_descriptor(&event_descriptor) else {
                continue;
            };

            match result {
                Err(BlockBuilderError::Rejected) => panic!("rejected"),
                Err(BlockBuilderError::PayloadExpired) => panic!("payload expired"),
                Err(BlockBuilderError::ImplicitDrop {
                    block: _,
                    reassembly_error,
                }) => panic!("implicit drop: {reassembly_error:?}"),
                Ok(CommitStateBlockUpdate {
                    block,
                    state,
                    abandoned,
                }) => {
                    eprintln!(
                        "[{}] -> {:?} {state:?}",
                        block.start.block_tag.block_number, block.start.block_tag.id
                    );

                    for abandoned in abandoned {
                        eprintln!(" -> {:?} abandoned", abandoned.start.block_tag.id)
                    }
                }
            }

            eprintln!("{block_builder:#?}");
        }
    }

    #[test]
    fn basic_test_ethereum_mainnet() {
        const SNAPSHOT_NAME: &str = "ETHEREUM_MAINNET_30B_15M";
        const SNAPSHOT_ZSTD_BYTES: &[u8] =
            include_bytes!("../../../test/data/exec-events-emn-30b-15m/snapshot.zst");

        run_commit_state_block_builder(SNAPSHOT_NAME, SNAPSHOT_ZSTD_BYTES);
    }

    #[ignore]
    #[test]
    fn basic_test_monad_testnet() {
        const SNAPSHOT_NAME: &str = "MONAD_DEVNET_500B_GENESIS";
        const SNAPSHOT_ZSTD_BYTES: &[u8] =
            include_bytes!("../../../test/data/exec-events-mdn-500b-genesis/snapshot.zst");

        run_commit_state_block_builder(SNAPSHOT_NAME, SNAPSHOT_ZSTD_BYTES);
    }
}
