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

use std::ptr::NonNull;

use alloy_eips::eip4895::Withdrawal;
use alloy_primitives::{Address, FixedBytes, B256, U256, U64};
use serde::{Deserialize, Serialize};

use crate::ffi;

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct BlockOverride {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub number: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub time: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub gas_limit: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fee_recipient: Option<Address>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prev_randao: Option<B256>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base_fee_per_gas: Option<U256>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub withdrawals: Vec<Withdrawal>,
}

pub(crate) struct CBlockOverrideVec {
    c_handle: NonNull<ffi::monad_block_override_vec>,
}

impl CBlockOverrideVec {
    pub(crate) fn with_capacity(size: usize) -> Option<Self> {
        NonNull::new(unsafe { ffi::monad_block_override_vec_create(size) })
            .map(|c_handle| Self { c_handle })
    }

    pub(crate) fn as_mut_ptr(&mut self) -> *mut ffi::monad_block_override_vec {
        self.c_handle.as_ptr()
    }

    pub(crate) fn set_number_at(&mut self, i: usize, number: u64) {
        unsafe {
            ffi::set_block_override_number_at(self.as_mut_ptr(), i, number);
        }
    }

    pub(crate) fn set_time_at(&mut self, i: usize, time: u64) {
        unsafe {
            ffi::set_block_override_time_at(self.as_mut_ptr(), i, time);
        }
    }

    pub(crate) fn set_gas_limit_at(&mut self, i: usize, gas_limit: u64) {
        unsafe {
            ffi::set_block_override_gas_limit_at(self.as_mut_ptr(), i, gas_limit);
        }
    }

    pub(crate) fn set_fee_recipient_at(&mut self, i: usize, fee_recipient: &Address) {
        let fee_recipient_bytes: &[u8] = fee_recipient.as_slice();
        unsafe {
            ffi::set_block_override_fee_recipient_at(
                self.as_mut_ptr(),
                i,
                fee_recipient_bytes.as_ptr(),
                fee_recipient_bytes.len(),
            );
        }
    }

    pub(crate) fn set_prev_randao_at(&mut self, i: usize, prev_randao: &FixedBytes<32>) {
        let prev_randao_bytes: &[u8] = prev_randao.as_slice();
        unsafe {
            ffi::set_block_override_prev_randao_at(
                self.as_mut_ptr(),
                i,
                prev_randao_bytes.as_ptr(),
                prev_randao_bytes.len(),
            );
        }
    }

    pub(crate) fn set_base_fee_per_gas_at(&mut self, i: usize, base_fee_per_gas: &U256) {
        let base_fee_per_gas_vec = base_fee_per_gas.to_be_bytes_vec();
        unsafe {
            ffi::set_block_override_base_fee_per_gas_at(
                self.as_mut_ptr(),
                i,
                base_fee_per_gas_vec.as_ptr(),
                base_fee_per_gas_vec.len(),
            );
        }
    }

    pub(crate) fn add_withdrawal_at(&mut self, i: usize, withdrawal: &Withdrawal) {
        let address_bytes: &[u8] = withdrawal.address.as_slice();
        unsafe {
            ffi::add_block_override_withdrawal_at(
                self.as_mut_ptr(),
                i,
                withdrawal.index,
                withdrawal.validator_index,
                withdrawal.amount,
                address_bytes.as_ptr(),
                address_bytes.len(),
            );
        }
    }
}

impl Drop for CBlockOverrideVec {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_block_override_vec_destroy(self.c_handle.as_ptr());
        }
    }
}
