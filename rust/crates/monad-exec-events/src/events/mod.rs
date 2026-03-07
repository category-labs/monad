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

use monad_event_ring::{
    ffi::{monad_event_content_type, monad_event_record_error, MONAD_EVENT_CONTENT_TYPE_EXEC},
    EventDecoder, EventDescriptorInfo,
};

use self::bytes::{ref_from_bytes, ref_from_bytes_with_trailing};
use crate::ffi::{
    self, g_monad_exec_event_schema_hash, monad_exec_account_access,
    monad_exec_account_access_list_header, monad_exec_block_end, monad_exec_block_finalized,
    monad_exec_block_qc, monad_exec_block_reject, monad_exec_block_start,
    monad_exec_block_verified, monad_exec_event_type, monad_exec_evm_error,
    monad_exec_storage_access, monad_exec_txn_access_list_entry, monad_exec_txn_auth_list_entry,
    monad_exec_txn_call_frame, monad_exec_txn_evm_output, monad_exec_txn_header_start,
    monad_exec_txn_log, monad_exec_txn_reject,
};

mod bytes;

/// Marker type that implements [`EventDecoder`] for monad execution events.
#[derive(Debug)]
pub struct ExecEventDecoder;

/// Owned rust enum for monad execution events.
///
/// This type uses the bindgen generated monad-execution C types to enable efficient memcpys of
/// event ring payloads.
///
/// See [`ExecEventRef`] for the zero-copy ref version.
#[allow(missing_docs)]
#[derive(Clone, Debug, strum::EnumDiscriminants)]
#[strum_discriminants(name(ExecEventType), allow(missing_docs))]
pub enum ExecEvent {
    RecordError(monad_event_record_error),
    BlockStart(monad_exec_block_start),
    BlockReject(monad_exec_block_reject),
    BlockPerfEvmEnter,
    BlockPerfEvmExit,
    BlockEnd(monad_exec_block_end),
    BlockQC(monad_exec_block_qc),
    BlockFinalized(monad_exec_block_finalized),
    BlockVerified(monad_exec_block_verified),
    TxnHeaderStart {
        txn_index: usize,
        txn_header_start: monad_exec_txn_header_start,
        data_bytes: Box<[u8]>,
        blob_bytes: Box<[u8]>,
    },
    TxnAccessListEntry {
        txn_index: usize,
        txn_access_list_entry: monad_exec_txn_access_list_entry,
        storage_key_bytes: Box<[u8]>,
    },
    TxnAuthListEntry {
        txn_index: usize,
        txn_auth_list_entry: monad_exec_txn_auth_list_entry,
    },
    TxnHeaderEnd,
    TxnReject {
        txn_index: usize,
        reject: monad_exec_txn_reject,
    },
    TxnPerfEvmEnter,
    TxnPerfEvmExit,
    TxnEvmOutput {
        txn_index: usize,
        output: monad_exec_txn_evm_output,
    },
    TxnLog {
        txn_index: usize,
        txn_log: monad_exec_txn_log,
        topic_bytes: Box<[u8]>,
        data_bytes: Box<[u8]>,
    },
    TxnCallFrame {
        txn_index: usize,
        txn_call_frame: monad_exec_txn_call_frame,
        input_bytes: Box<[u8]>,
        return_bytes: Box<[u8]>,
    },
    TxnEnd,
    AccountAccessListHeader(monad_exec_account_access_list_header),
    AccountAccess(monad_exec_account_access),
    StorageAccess(monad_exec_storage_access),
    EvmError(monad_exec_evm_error),
}

/// Ref rust enum for monad execution events.
///
/// This enum should only be used with the zero-copy event ring API to enable zero-copy access to
/// event ring payloads.
///
/// See [`ExecEvent`] for the owned version.
#[allow(missing_docs)]
#[derive(Copy, Clone, Debug)]
pub enum ExecEventRef<'ring> {
    RecordError(&'ring monad_event_record_error),
    BlockStart(&'ring monad_exec_block_start),
    BlockReject(&'ring monad_exec_block_reject),
    BlockPerfEvmEnter,
    BlockPerfEvmExit,
    BlockEnd(&'ring monad_exec_block_end),
    BlockQC(&'ring monad_exec_block_qc),
    BlockFinalized(&'ring monad_exec_block_finalized),
    BlockVerified(&'ring monad_exec_block_verified),
    TxnHeaderStart {
        txn_index: usize,
        txn_header_start: &'ring monad_exec_txn_header_start,
        data_bytes: &'ring [u8],
        blob_bytes: &'ring [u8],
    },
    TxnAccessListEntry {
        txn_index: usize,
        txn_access_list_entry: &'ring monad_exec_txn_access_list_entry,
        storage_key_bytes: &'ring [u8],
    },
    TxnAuthListEntry {
        txn_index: usize,
        txn_auth_list_entry: &'ring monad_exec_txn_auth_list_entry,
    },
    TxnHeaderEnd,
    TxnReject {
        txn_index: usize,
        reject: &'ring monad_exec_txn_reject,
    },
    TxnPerfEvmEnter,
    TxnPerfEvmExit,
    TxnEvmOutput {
        txn_index: usize,
        output: &'ring monad_exec_txn_evm_output,
    },
    TxnLog {
        txn_index: usize,
        txn_log: &'ring monad_exec_txn_log,
        topic_bytes: &'ring [u8],
        data_bytes: &'ring [u8],
    },
    TxnCallFrame {
        txn_index: usize,
        txn_call_frame: &'ring monad_exec_txn_call_frame,
        input_bytes: &'ring [u8],
        return_bytes: &'ring [u8],
    },
    TxnEnd,
    AccountAccessListHeader(&'ring monad_exec_account_access_list_header),
    AccountAccess(&'ring monad_exec_account_access),
    StorageAccess(&'ring monad_exec_storage_access),
    EvmError(&'ring monad_exec_evm_error),
}

impl ExecEventType {
    pub(crate) fn as_c_event_type(self) -> monad_exec_event_type {
        match self {
            ExecEventType::RecordError => ffi::MONAD_EXEC_RECORD_ERROR,
            ExecEventType::BlockStart => ffi::MONAD_EXEC_BLOCK_START,
            ExecEventType::BlockReject => ffi::MONAD_EXEC_BLOCK_REJECT,
            ExecEventType::BlockPerfEvmEnter => ffi::MONAD_EXEC_BLOCK_PERF_EVM_ENTER,
            ExecEventType::BlockPerfEvmExit => ffi::MONAD_EXEC_BLOCK_PERF_EVM_EXIT,
            ExecEventType::BlockEnd => ffi::MONAD_EXEC_BLOCK_END,
            ExecEventType::BlockQC => ffi::MONAD_EXEC_BLOCK_QC,
            ExecEventType::BlockFinalized => ffi::MONAD_EXEC_BLOCK_FINALIZED,
            ExecEventType::BlockVerified => ffi::MONAD_EXEC_BLOCK_VERIFIED,
            ExecEventType::TxnHeaderStart => ffi::MONAD_EXEC_TXN_HEADER_START,
            ExecEventType::TxnAccessListEntry => ffi::MONAD_EXEC_TXN_ACCESS_LIST_ENTRY,
            ExecEventType::TxnAuthListEntry => ffi::MONAD_EXEC_TXN_AUTH_LIST_ENTRY,
            ExecEventType::TxnHeaderEnd => ffi::MONAD_EXEC_TXN_HEADER_END,
            ExecEventType::TxnReject => ffi::MONAD_EXEC_TXN_REJECT,
            ExecEventType::TxnPerfEvmEnter => ffi::MONAD_EXEC_TXN_PERF_EVM_ENTER,
            ExecEventType::TxnPerfEvmExit => ffi::MONAD_EXEC_TXN_PERF_EVM_EXIT,
            ExecEventType::TxnEvmOutput => ffi::MONAD_EXEC_TXN_EVM_OUTPUT,
            ExecEventType::TxnLog => ffi::MONAD_EXEC_TXN_LOG,
            ExecEventType::TxnCallFrame => ffi::MONAD_EXEC_TXN_CALL_FRAME,
            ExecEventType::TxnEnd => ffi::MONAD_EXEC_TXN_END,
            ExecEventType::AccountAccessListHeader => ffi::MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER,
            ExecEventType::AccountAccess => ffi::MONAD_EXEC_ACCOUNT_ACCESS,
            ExecEventType::StorageAccess => ffi::MONAD_EXEC_STORAGE_ACCESS,
            ExecEventType::EvmError => ffi::MONAD_EXEC_EVM_ERROR,
        }
    }
}

impl<'ring> ExecEventRef<'ring> {
    /// Converts the [`ExecEventRef`] to its owned variant [`ExecEvent`].
    pub fn into_owned(self) -> ExecEvent {
        match self {
            Self::RecordError(record_error) => ExecEvent::RecordError(*record_error),
            Self::BlockStart(block_start) => ExecEvent::BlockStart(*block_start),
            Self::BlockReject(block_reject) => ExecEvent::BlockReject(*block_reject),
            Self::BlockPerfEvmEnter => ExecEvent::BlockPerfEvmEnter,
            Self::BlockPerfEvmExit => ExecEvent::BlockPerfEvmExit,
            Self::BlockEnd(block_end) => ExecEvent::BlockEnd(*block_end),
            Self::BlockQC(block_qc) => ExecEvent::BlockQC(*block_qc),
            Self::BlockFinalized(block_finalized) => ExecEvent::BlockFinalized(*block_finalized),
            Self::BlockVerified(block_verified) => ExecEvent::BlockVerified(*block_verified),
            Self::TxnHeaderStart {
                txn_index,
                txn_header_start: txn_start,
                data_bytes,
                blob_bytes: blobs,
            } => ExecEvent::TxnHeaderStart {
                txn_index,
                txn_header_start: *txn_start,
                data_bytes: data_bytes.to_vec().into_boxed_slice(),
                blob_bytes: blobs.to_vec().into_boxed_slice(),
            },
            Self::TxnAccessListEntry {
                txn_index,
                txn_access_list_entry,
                storage_key_bytes: storage_keys,
            } => ExecEvent::TxnAccessListEntry {
                txn_index,
                txn_access_list_entry: *txn_access_list_entry,
                storage_key_bytes: storage_keys.to_vec().into_boxed_slice(),
            },
            Self::TxnAuthListEntry {
                txn_index,
                txn_auth_list_entry,
            } => ExecEvent::TxnAuthListEntry {
                txn_index,
                txn_auth_list_entry: *txn_auth_list_entry,
            },
            Self::TxnHeaderEnd => ExecEvent::TxnHeaderEnd,
            Self::TxnReject { txn_index, reject } => ExecEvent::TxnReject {
                txn_index,
                reject: *reject,
            },
            Self::TxnPerfEvmEnter => ExecEvent::TxnPerfEvmEnter,
            Self::TxnPerfEvmExit => ExecEvent::TxnPerfEvmExit,
            Self::TxnEvmOutput { txn_index, output } => ExecEvent::TxnEvmOutput {
                txn_index,
                output: *output,
            },
            Self::TxnLog {
                txn_index,
                txn_log,
                topic_bytes,
                data_bytes,
            } => ExecEvent::TxnLog {
                txn_index,
                txn_log: *txn_log,
                topic_bytes: topic_bytes.to_vec().into_boxed_slice(),
                data_bytes: data_bytes.to_vec().into_boxed_slice(),
            },
            Self::TxnCallFrame {
                txn_index,
                txn_call_frame,
                input_bytes,
                return_bytes,
            } => ExecEvent::TxnCallFrame {
                txn_index,
                txn_call_frame: *txn_call_frame,
                input_bytes: input_bytes.to_vec().into_boxed_slice(),
                return_bytes: return_bytes.to_vec().into_boxed_slice(),
            },
            Self::TxnEnd => ExecEvent::TxnEnd,
            Self::AccountAccessListHeader(account_access_list_header) => {
                ExecEvent::AccountAccessListHeader(*account_access_list_header)
            }
            Self::AccountAccess(account_access) => ExecEvent::AccountAccess(*account_access),
            Self::StorageAccess(storage_access) => ExecEvent::StorageAccess(*storage_access),
            Self::EvmError(evm_error) => ExecEvent::EvmError(*evm_error),
        }
    }
}

/// Flow info for execution events.
pub struct ExecEventRingFlowInfo {
    block_seqno: u64,
    txn_idx: Option<usize>,
    account_idx: u64,
}

impl EventDecoder for ExecEventDecoder {
    fn ring_content_ctype() -> monad_event_content_type {
        MONAD_EVENT_CONTENT_TYPE_EXEC
    }

    fn ring_schema_hash() -> &'static [u8; 32] {
        unsafe { &g_monad_exec_event_schema_hash }
    }

    type FlowInfo = ExecEventRingFlowInfo;

    fn transmute_flow_info(user: [u64; 4]) -> Self::FlowInfo {
        Self::FlowInfo {
            block_seqno: user[ffi::MONAD_FLOW_BLOCK_SEQNO as usize],
            txn_idx: user[ffi::MONAD_FLOW_TXN_ID as usize]
                .checked_sub(1)
                .map(|txn_idx| txn_idx.try_into().unwrap()),
            account_idx: user[ffi::MONAD_FLOW_ACCOUNT_INDEX as usize],
        }
    }

    type Event = ExecEvent;
    type EventRef<'ring> = ExecEventRef<'ring>;

    fn raw_to_event_ref<'ring>(
        info: EventDescriptorInfo<Self>,
        bytes: &'ring [u8],
    ) -> Self::EventRef<'ring> {
        match info.event_type {
            ffi::MONAD_EXEC_NONE => {
                panic!("ExecEventDecoder encountered NONE event_type");
            }
            ffi::MONAD_EXEC_RECORD_ERROR => {
                ExecEventRef::RecordError(ref_from_bytes(bytes).expect("RecordError event valid"))
            }
            ffi::MONAD_EXEC_BLOCK_START => {
                ExecEventRef::BlockStart(ref_from_bytes(bytes).expect("BlockStart event valid"))
            }
            ffi::MONAD_EXEC_BLOCK_REJECT => {
                ExecEventRef::BlockReject(ref_from_bytes(bytes).expect("BlockReject event valid"))
            }
            ffi::MONAD_EXEC_BLOCK_PERF_EVM_ENTER => {
                assert_eq!(bytes.len(), 0, "BlockPerfEvmEnter payload is empty");
                ExecEventRef::BlockPerfEvmEnter
            }
            ffi::MONAD_EXEC_BLOCK_PERF_EVM_EXIT => {
                assert_eq!(bytes.len(), 0, "BlockPerfEvmExit payload is empty");
                ExecEventRef::BlockPerfEvmExit
            }
            ffi::MONAD_EXEC_BLOCK_END => {
                ExecEventRef::BlockEnd(ref_from_bytes(bytes).expect("BlockEnd event valid"))
            }
            ffi::MONAD_EXEC_BLOCK_QC => {
                ExecEventRef::BlockQC(ref_from_bytes(bytes).expect("BlockQC event valid"))
            }
            ffi::MONAD_EXEC_BLOCK_FINALIZED => ExecEventRef::BlockFinalized(
                ref_from_bytes(bytes).expect("BlockFinalized event valid"),
            ),
            ffi::MONAD_EXEC_BLOCK_VERIFIED => ExecEventRef::BlockVerified(
                ref_from_bytes(bytes).expect("BlockVerified event valid"),
            ),
            ffi::MONAD_EXEC_TXN_HEADER_START => {
                let (txn_header_start, [data_bytes, blob_bytes]) =
                    ref_from_bytes_with_trailing::<monad_exec_txn_header_start, 2>(
                        bytes,
                        |txn_header_start| {
                            [
                                txn_header_start.txn_header.data_length.try_into().unwrap(),
                                TryInto::<usize>::try_into(
                                    txn_header_start.txn_header.blob_versioned_hash_length,
                                )
                                .unwrap()
                                .checked_mul(size_of::<ffi::monad_c_bytes32>())
                                .unwrap(),
                            ]
                        },
                    )
                    .expect("TxnHeaderStart event valid");

                ExecEventRef::TxnHeaderStart {
                    txn_index: info
                        .flow_info
                        .txn_idx
                        .expect("TxnHeaderStart event has txn_idx in flow_info"),
                    txn_header_start,
                    data_bytes,
                    blob_bytes,
                }
            }
            ffi::MONAD_EXEC_TXN_ACCESS_LIST_ENTRY => {
                let (txn_access_list_entry, [storage_key_bytes]) =
                    ref_from_bytes_with_trailing::<monad_exec_txn_access_list_entry, 1>(
                        bytes,
                        |txn_access_list_entry| {
                            [TryInto::<usize>::try_into(
                                txn_access_list_entry.entry.storage_key_count,
                            )
                            .unwrap()
                            .checked_mul(size_of::<ffi::monad_c_bytes32>())
                            .unwrap()]
                        },
                    )
                    .expect("TxnAccessListEntry event valid");

                ExecEventRef::TxnAccessListEntry {
                    txn_index: info
                        .flow_info
                        .txn_idx
                        .expect("TxnAccessListEntry event has txn_idx in flow_info"),
                    txn_access_list_entry,
                    storage_key_bytes,
                }
            }
            ffi::MONAD_EXEC_TXN_AUTH_LIST_ENTRY => ExecEventRef::TxnAuthListEntry {
                txn_index: info
                    .flow_info
                    .txn_idx
                    .expect("TxnAuthListEntry event has txn_idx in flow_info"),
                txn_auth_list_entry: ref_from_bytes(bytes).expect("TxnAuthListEntry event valid"),
            },
            ffi::MONAD_EXEC_TXN_HEADER_END => {
                assert_eq!(bytes.len(), 0, "TxnHeaderEnd payload is empty");
                ExecEventRef::TxnHeaderEnd
            }
            ffi::MONAD_EXEC_TXN_REJECT => ExecEventRef::TxnReject {
                txn_index: info
                    .flow_info
                    .txn_idx
                    .expect("TxnReject event has txn_idx in flow_info"),
                reject: ref_from_bytes(bytes).expect("TxnReject event valid"),
            },
            ffi::MONAD_EXEC_TXN_PERF_EVM_ENTER => {
                assert_eq!(bytes.len(), 0, "TxnPerfEvmEnter payload is empty");
                ExecEventRef::TxnPerfEvmEnter
            }
            ffi::MONAD_EXEC_TXN_PERF_EVM_EXIT => {
                assert_eq!(bytes.len(), 0, "TxnPerfEvmExit payload is empty");
                ExecEventRef::TxnPerfEvmExit
            }
            ffi::MONAD_EXEC_TXN_EVM_OUTPUT => ExecEventRef::TxnEvmOutput {
                txn_index: info
                    .flow_info
                    .txn_idx
                    .expect("TxnEvmOutput event has txn_idx in flow_info"),
                output: ref_from_bytes(bytes).expect("TxnEvmOutput event valid"),
            },
            ffi::MONAD_EXEC_TXN_LOG => {
                let (txn_log, [topic_bytes, data_bytes]) =
                    ref_from_bytes_with_trailing::<monad_exec_txn_log, 2>(bytes, |txn_log| {
                        [
                            Into::<usize>::into(txn_log.topic_count)
                                .checked_mul(size_of::<ffi::monad_c_bytes32>())
                                .unwrap(),
                            txn_log.data_length.try_into().unwrap(),
                        ]
                    })
                    .expect("TxnLog event valid");

                ExecEventRef::TxnLog {
                    txn_index: info
                        .flow_info
                        .txn_idx
                        .expect("TxnLog event has txn_idx in flow_info"),
                    txn_log,
                    topic_bytes,
                    data_bytes,
                }
            }
            ffi::MONAD_EXEC_TXN_CALL_FRAME => {
                let (txn_call_frame, [input_bytes, return_bytes]) =
                    ref_from_bytes_with_trailing::<monad_exec_txn_call_frame, 2>(
                        bytes,
                        |txn_call_frame| {
                            [
                                txn_call_frame.input_length.try_into().unwrap(),
                                txn_call_frame.return_length.try_into().unwrap(),
                            ]
                        },
                    )
                    .expect("TxnCallFrame event valid");

                ExecEventRef::TxnCallFrame {
                    txn_index: info
                        .flow_info
                        .txn_idx
                        .expect("TxnCallFrame event has txn_idx in flow_info"),
                    txn_call_frame,
                    input_bytes,
                    return_bytes,
                }
            }
            ffi::MONAD_EXEC_TXN_END => {
                assert_eq!(bytes.len(), 0, "TxnEnd payload is empty");
                ExecEventRef::TxnEnd
            }
            ffi::MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER => ExecEventRef::AccountAccessListHeader(
                ref_from_bytes(bytes).expect("AccountAccessListHeader event valid"),
            ),
            ffi::MONAD_EXEC_ACCOUNT_ACCESS => ExecEventRef::AccountAccess(
                ref_from_bytes(bytes).expect("AccountAccess event valid"),
            ),
            ffi::MONAD_EXEC_STORAGE_ACCESS => ExecEventRef::StorageAccess(
                ref_from_bytes(bytes).expect("StorageAccess event valid"),
            ),
            ffi::MONAD_EXEC_EVM_ERROR => {
                ExecEventRef::EvmError(ref_from_bytes(bytes).expect("EvmError event valid"))
            }
            event_type => panic!("ExecEventDecoder encountered unknown event_type {event_type}"),
        }
    }

    fn event_ref_to_event<'ring>(event_ref: Self::EventRef<'ring>) -> Self::Event {
        Self::EventRef::into_owned(event_ref)
    }
}

#[cfg(test)]
mod test {
    use monad_event_ring::{DecodedEventRing, EventNextResult, SnapshotEventRing};

    use crate::ExecEventDecoder;

    #[test]
    fn basic_test() {
        const SNAPSHOT_NAME: &str = "ETHEREUM_MAINNET_30B_15M";
        const SNAPSHOT_ZSTD_BYTES: &[u8] =
            include_bytes!("../../test/data/exec-events-emn-30b-15m/snapshot.zst");

        let snapshot = SnapshotEventRing::<ExecEventDecoder>::new_from_zstd_bytes(
            SNAPSHOT_ZSTD_BYTES,
            SNAPSHOT_NAME,
        )
        .unwrap();

        let mut event_reader = snapshot.create_reader();

        loop {
            match event_reader.next_descriptor() {
                EventNextResult::Gap => panic!("snapshot cannot gap"),
                EventNextResult::NotReady => break,
                EventNextResult::Ready(event_descriptor) => {
                    let event = event_descriptor.try_read();

                    eprintln!("event: {event:#?}");
                }
            }
        }
    }
}
