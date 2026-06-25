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
    ffi::{CStr, CString},
    path::Path,
    ptr::NonNull,
};

use tracing::info;

pub use self::{
    call::EthCallRequest,
    simulate::{FailureSimulateResult, SimulateResult, SuccessSimulateResult},
};
use crate::ffi;

mod call;
mod simulate;
mod trace;

pub(super) const ETH_CALL_SUCCESS: i32 = 0;
pub(super) const EVMC_OUT_OF_GAS: i32 = 3;
pub(super) const EVMC_MONAD_RESERVE_BALANCE_VIOLATION: i32 = 18;

#[derive(Debug)]
pub struct MonadExecutor {
    eth_call_executor: *mut ffi::monad_executor,
}

unsafe impl Send for MonadExecutor {}
unsafe impl Sync for MonadExecutor {}

impl MonadExecutor {
    pub fn new(
        low_pool_config: ffi::PoolConfig,
        high_pool_config: ffi::PoolConfig,
        block_pool_config: ffi::PoolConfig,
        tx_exec_num_fibers: u32,
        node_lru_max_mem: u64,
        triedb_path: &Path,
    ) -> Self {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let dbpath = CString::new(triedb_path.to_str().expect("invalid path"))
            .expect("failed to create CString");

        let eth_call_executor = unsafe {
            ffi::monad_executor_create(
                low_pool_config,
                high_pool_config,
                block_pool_config,
                tx_exec_num_fibers,
                node_lru_max_mem,
                dbpath.as_c_str().as_ptr(),
            )
        };

        Self { eth_call_executor }
    }
}

impl Drop for MonadExecutor {
    fn drop(&mut self) {
        info!("dropping eth_call_executor");
        unsafe {
            ffi::monad_executor_destroy(self.eth_call_executor);
        }
        info!("eth_call_executor successfully destroyed");
    }
}

pub(crate) struct MonadExecutorResult {
    inner: NonNull<ffi::monad_executor_result>,
}

impl MonadExecutorResult {
    pub fn from_c_handle(c_handle: *mut ffi::monad_executor_result) -> Option<Self> {
        NonNull::new(c_handle).map(|inner| Self { inner })
    }

    pub fn status_code(&self) -> i32 {
        unsafe { self.inner.as_ref() }.status_code
    }

    pub fn encoded_trace(&self) -> Result<Box<[u8]>, ()> {
        let this = unsafe { self.inner.as_ref() };

        if this.encoded_trace_len == 0 {
            return Ok(Box::new([]));
        }

        if this.encoded_trace.is_null() {
            return Err(());
        }

        Ok(Box::from(unsafe {
            std::slice::from_raw_parts(this.encoded_trace, this.encoded_trace_len)
        }))
    }

    pub fn message(&self) -> String {
        let cstr_msg = unsafe { CStr::from_ptr(self.inner.as_ref().message.cast()) };

        String::from(
            cstr_msg
                .to_str()
                .unwrap_or("execution error: message invalid utf-8"),
        )
    }
}

impl Drop for MonadExecutorResult {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_executor_result_release(self.inner.as_ptr());
        }
    }
}

#[derive(Clone, Debug)]
pub enum CallResult {
    Success(SuccessCallResult),
    Failure(FailureCallResult),
    Revert(RevertCallResult), // only used for trace
}

#[derive(Clone, Debug, Default)]
pub struct SuccessCallResult {
    pub gas_used: u64,
    pub gas_refund: u64,
    // We interpret this as rlp encoded CallFrames for debug_traceCall
    pub output_data: Vec<u8>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum EthCallResult {
    Success,
    OutOfGas,
    ExecutionError,
    ReserveBalanceViolation,
    #[default]
    OtherError,
}

#[derive(Clone, Debug, Default)]
pub struct FailureCallResult {
    pub error_code: EthCallResult,
    pub gas_used: u64,
    pub gas_refund: u64,
    pub message: String,
    pub data: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct RevertCallResult {
    pub trace: Vec<u8>,
}

pub(super) struct SenderContext {
    sender: futures::channel::oneshot::Sender<*mut ffi::monad_executor_result>,
}

/// # Safety
/// This should be used only as a callback for monad_eth_call_executor_submit
///
/// This function is called when the eth_call is finished and the result is returned over the
/// channel
pub(super) unsafe extern "C" fn eth_call_submit_callback(
    result: *mut ffi::monad_executor_result,
    user: *mut std::ffi::c_void,
) {
    let user = unsafe { Box::from_raw(user as *mut SenderContext) };

    let _ = user.sender.send(result);
}

pub fn decode_revert_message(output_data: &[u8]) -> Option<String> {
    // https://docs.soliditylang.org/en/latest/control-structures.html#revert
    alloy_sol_types::decode_revert_reason(output_data).and_then(|message| {
        let parsed_message = message
            .strip_prefix("revert: ")
            .or_else(|| message.strip_prefix("panic: "))
            .unwrap_or(&message)
            .trim();
        if parsed_message.is_empty() {
            None
        } else {
            Some(parsed_message.to_string())
        }
    })
}

#[cfg(test)]
mod tests {
    use alloy_primitives::hex;

    use super::*;

    #[test]
    fn test_decode_revert_message() {
        // https://github.com/ethereum/execution-apis/blob/37c2b9e/tests/eth_call/call-revert-abi-error.io
        let data = hex::decode(
            "0x08c379a00000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000a75736572206572726f72"
        ).unwrap();
        let message = decode_revert_message(&data).unwrap();
        assert_eq!(message, String::from("user error"));

        // https://github.com/ethereum/execution-apis/blob/37c2b9e/tests/eth_call/call-revert-abi-panic.io
        let data = hex::decode(
            "0x4e487b710000000000000000000000000000000000000000000000000000000000000001",
        )
        .unwrap();
        let message = decode_revert_message(&data).unwrap();
        assert_eq!(message, String::from("assertion failed (0x01)"));
    }
}
