// Copyright (C) 2025-26 Category Labs, Inc.
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

use cxx::{CxxVector, UniquePtr};

use crate::TriedbRoHandle;

#[derive(Clone, Copy, Debug)]
pub struct Validator {
    pub secp_pubkey: [u8; 33],
    pub bls_pubkey: [u8; 48],
    pub stake: [u8; 32],
}

pub struct ValidatorSet {
    inner: UniquePtr<CxxVector<crate::ffi::Validator>>,
}

impl ValidatorSet {
    fn new(inner: UniquePtr<CxxVector<crate::ffi::Validator>>) -> Option<Self> {
        (!inner.is_null()).then_some(Self { inner })
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = Validator> + '_ {
        self.inner
            .as_ref()
            .expect("ValidatorSet invariant: inner is non-null")
            .iter()
            .map(|validator| Validator {
                secp_pubkey: crate::ffi::validator_secp_pubkey(validator),
                bls_pubkey: crate::ffi::validator_bls_pubkey(validator),
                stake: crate::ffi::validator_stake(validator),
            })
    }
}

pub trait TriedbValSetRead {
    fn validator_set_at_block(
        &mut self,
        block_num: usize,
        requested_epoch: u64,
    ) -> Option<ValidatorSet>;
}

impl TriedbValSetRead for TriedbRoHandle {
    fn validator_set_at_block(
        &mut self,
        block_num: usize,
        requested_epoch: u64,
    ) -> Option<ValidatorSet> {
        ValidatorSet::new(crate::ffi::triedb_ro_read_valset(
            self.inner_mut(),
            block_num,
            requested_epoch,
        ))
    }
}
