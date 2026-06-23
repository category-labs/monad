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

use std::{collections::HashMap, ptr::NonNull};

use alloy_primitives::{Address, Bytes, FixedBytes, B256, U256, U64};
use serde::{Deserialize, Serialize};

use crate::ffi;

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum StorageOverride {
    State(HashMap<B256, B256>),
    StateDiff(HashMap<B256, B256>),
}

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct StateOverrideObject {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub balance: Option<U256>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub nonce: Option<U64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<Bytes>,
    #[serde(flatten, default, skip_serializing_if = "Option::is_none")]
    pub storage_override: Option<StorageOverride>,
}

pub type StateOverrideSet = HashMap<Address, StateOverrideObject>;

pub(crate) struct CStateOverrideVec {
    c_handle: NonNull<ffi::monad_state_override_vec>,
}

impl CStateOverrideVec {
    pub(crate) fn with_capacity(size: usize) -> Option<Self> {
        NonNull::new(unsafe { ffi::monad_state_override_vec_create(size) })
            .map(|c_handle| Self { c_handle })
    }

    pub(crate) fn as_mut_ptr(&mut self) -> *mut ffi::monad_state_override_vec {
        self.c_handle.as_ptr()
    }

    pub(crate) fn add_address_at(&mut self, at: usize, addr: &Address) {
        let addr: &[u8] = addr.as_slice();
        unsafe {
            ffi::add_override_address_at(self.as_mut_ptr(), at, addr.as_ptr(), addr.len());
        }
    }

    pub(crate) fn set_balance_at(&mut self, at: usize, addr: &Address, balance: &U256) {
        // Big Endianness is to match with decode in eth_call.cpp (intx::be::load)
        let balance_bytes = balance.to_be_bytes_vec();
        let addr: &[u8] = addr.as_slice();
        unsafe {
            ffi::set_override_balance_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                balance_bytes.as_ptr(),
                balance_bytes.len(),
            );
        }
    }

    pub(crate) fn set_nonce_at(&mut self, at: usize, addr: &Address, nonce: u64) {
        let addr: &[u8] = addr.as_slice();
        unsafe {
            ffi::set_override_nonce_at(self.as_mut_ptr(), at, addr.as_ptr(), addr.len(), nonce);
        }
    }

    pub(crate) fn set_code_at(&mut self, at: usize, addr: &Address, code: &Bytes) {
        let addr: &[u8] = addr.as_slice();
        unsafe {
            ffi::set_override_code_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                code.as_ptr(),
                code.len(),
            );
        }
    }

    pub(crate) fn set_state_at(
        &mut self,
        at: usize,
        addr: &Address,
        key: &FixedBytes<32>,
        value: &FixedBytes<32>,
    ) {
        let addr: &[u8] = addr.as_slice();
        unsafe {
            ffi::set_override_state_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                key.as_ptr(),
                key.len(),
                value.as_ptr(),
                value.len(),
            );
        }
    }

    pub(crate) fn set_state_diff_at(
        &mut self,
        at: usize,
        addr: &Address,
        key: &FixedBytes<32>,
        value: &FixedBytes<32>,
    ) {
        let addr: &[u8] = addr.as_slice();
        unsafe {
            ffi::set_override_state_diff_at(
                self.as_mut_ptr(),
                at,
                addr.as_ptr(),
                addr.len(),
                key.as_ptr(),
                key.len(),
                value.as_ptr(),
                value.len(),
            );
        }
    }
}

impl Drop for CStateOverrideVec {
    fn drop(&mut self) {
        unsafe {
            ffi::monad_state_override_vec_destroy(self.c_handle.as_ptr());
        }
    }
}
