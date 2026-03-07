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

//! This module contains low-level bindings to the monad execution client event types.

pub use self::bindings::{
    g_monad_exec_event_metadata, monad_c_access_list_entry, monad_c_address,
    monad_c_auth_list_entry, monad_c_bytes32, monad_c_eth_txn_header, monad_c_eth_txn_receipt,
    monad_c_uint256_ne, monad_exec_account_access, monad_exec_account_access_context,
    monad_exec_account_access_list_header, monad_exec_block_end, monad_exec_block_finalized,
    monad_exec_block_qc, monad_exec_block_reject, monad_exec_block_start, monad_exec_block_tag,
    monad_exec_block_verified, monad_exec_evm_error, monad_exec_storage_access,
    monad_exec_txn_access_list_entry, monad_exec_txn_auth_list_entry, monad_exec_txn_call_frame,
    monad_exec_txn_evm_output, monad_exec_txn_header_start, monad_exec_txn_log,
    monad_exec_txn_reject, MONAD_TXN_EIP1559, MONAD_TXN_EIP2930, MONAD_TXN_EIP4844,
    MONAD_TXN_EIP7702, MONAD_TXN_LEGACY,
};
pub(crate) use self::bindings::{
    g_monad_exec_event_schema_hash, monad_exec_event_type, MONAD_EXEC_ACCOUNT_ACCESS,
    MONAD_EXEC_ACCOUNT_ACCESS_LIST_HEADER, MONAD_EXEC_BLOCK_END, MONAD_EXEC_BLOCK_FINALIZED,
    MONAD_EXEC_BLOCK_PERF_EVM_ENTER, MONAD_EXEC_BLOCK_PERF_EVM_EXIT, MONAD_EXEC_BLOCK_QC,
    MONAD_EXEC_BLOCK_REJECT, MONAD_EXEC_BLOCK_START, MONAD_EXEC_BLOCK_VERIFIED,
    MONAD_EXEC_EVM_ERROR, MONAD_EXEC_NONE, MONAD_EXEC_RECORD_ERROR, MONAD_EXEC_STORAGE_ACCESS,
    MONAD_EXEC_TXN_ACCESS_LIST_ENTRY, MONAD_EXEC_TXN_AUTH_LIST_ENTRY, MONAD_EXEC_TXN_CALL_FRAME,
    MONAD_EXEC_TXN_END, MONAD_EXEC_TXN_EVM_OUTPUT, MONAD_EXEC_TXN_HEADER_END,
    MONAD_EXEC_TXN_HEADER_START, MONAD_EXEC_TXN_LOG, MONAD_EXEC_TXN_PERF_EVM_ENTER,
    MONAD_EXEC_TXN_PERF_EVM_EXIT, MONAD_EXEC_TXN_REJECT, MONAD_FLOW_ACCOUNT_INDEX,
    MONAD_FLOW_BLOCK_SEQNO, MONAD_FLOW_TXN_ID,
};

#[allow(
    dead_code,
    missing_docs,
    non_camel_case_types,
    non_upper_case_globals,
    rustdoc::broken_intra_doc_links
)]
mod bindings {
    use ::monad_event_ring::ffi::{monad_event_descriptor, monad_event_iterator, monad_event_ring};

    include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}

use ::monad_event_ring::ffi::{monad_event_descriptor, monad_event_iterator, monad_event_ring};

pub(crate) fn monad_exec_ring_get_block_number(
    c_event_ring: &monad_event_ring,
    c_event_descriptor: &monad_event_descriptor,
) -> Option<u64> {
    let mut block_number = 0;

    let success = unsafe {
        self::bindings::monad_exec_ring_get_block_number(
            c_event_ring,
            c_event_descriptor,
            &mut block_number,
        )
    };

    success.then_some(block_number)
}

pub(crate) fn monad_exec_ring_block_id_matches(
    c_event_ring: &monad_event_ring,
    c_event_descriptor: &monad_event_descriptor,
    block_id: &monad_c_bytes32,
) -> bool {
    unsafe {
        self::bindings::monad_exec_ring_block_id_matches(c_event_ring, c_event_descriptor, block_id)
    }
}

pub(crate) fn monad_exec_iter_consensus_prev(
    c_event_iterator: &mut monad_event_iterator,
    c_exec_event_filter: monad_exec_event_type,
) -> Option<monad_event_descriptor> {
    let mut c_event_descriptor: monad_event_descriptor = unsafe { std::mem::zeroed() };

    let success = unsafe {
        self::bindings::monad_exec_iter_consensus_prev(
            c_event_iterator,
            c_exec_event_filter,
            &mut c_event_descriptor,
        )
    };

    success.then_some(c_event_descriptor)
}

pub(crate) fn monad_exec_iter_block_number_prev(
    c_event_iterator: &mut monad_event_iterator,
    c_event_ring: &monad_event_ring,
    block_number: u64,
    c_exec_event_filter: monad_exec_event_type,
) -> Option<monad_event_descriptor> {
    let mut c_event_descriptor: monad_event_descriptor = unsafe { std::mem::zeroed() };

    let success = unsafe {
        self::bindings::monad_exec_iter_block_number_prev(
            c_event_iterator,
            c_event_ring,
            block_number,
            c_exec_event_filter,
            &mut c_event_descriptor,
        )
    };

    success.then_some(c_event_descriptor)
}

pub(crate) fn monad_exec_iter_block_id_prev(
    c_event_iterator: &mut monad_event_iterator,
    c_event_ring: &monad_event_ring,
    block_id: &monad_c_bytes32,
    c_exec_event_filter: monad_exec_event_type,
) -> Option<monad_event_descriptor> {
    let mut c_event_descriptor: monad_event_descriptor = unsafe { std::mem::zeroed() };

    let success = unsafe {
        self::bindings::monad_exec_iter_block_id_prev(
            c_event_iterator,
            c_event_ring,
            block_id,
            c_exec_event_filter,
            &mut c_event_descriptor,
        )
    };

    success.then_some(c_event_descriptor)
}
