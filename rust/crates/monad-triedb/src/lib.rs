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

use std::{path::Path, pin::Pin};

use cxx::UniquePtr;

pub use self::{
    read::{TriedbAsyncRead, TriedbNodeCursor, TriedbRead},
    validator::{TriedbValSetRead, Validator, ValidatorSet},
};

pub mod ffi;
mod read;
mod validator;

/// Borrowed view of a nibble-aligned key.
///
/// Odd nibble lengths are supported — the trailing low nibble of the last byte is ignored when
/// `nibble_len` is odd.
#[derive(Debug, Clone, Copy)]
pub struct NibblesView<'a> {
    bytes: &'a [u8],
    nibble_len: u8,
}

impl<'a> NibblesView<'a> {
    pub fn new(bytes: &'a [u8], nibble_len: u8) -> Option<Self> {
        ((nibble_len as usize).div_ceil(2) <= bytes.len()).then_some(Self { bytes, nibble_len })
    }

    /// Interprets the full slice as a byte-aligned key. Returns `None` if the slice is longer than
    /// 127 bytes (would overflow `u8` nibbles).
    pub fn from_bytes(bytes: &'a [u8]) -> Option<Self> {
        let nibble_len = u8::try_from(bytes.len().saturating_mul(2)).ok()?;
        Some(Self { bytes, nibble_len })
    }

    pub const fn empty() -> Self {
        Self {
            bytes: &[],
            nibble_len: 0,
        }
    }

    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub fn nibble_len(&self) -> u8 {
        self.nibble_len
    }
}

pub struct TriedbRoHandle {
    inner: UniquePtr<ffi::TriedbRoInner>,
}

impl std::fmt::Debug for TriedbRoHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TriedbRoHandle").finish_non_exhaustive()
    }
}

impl TriedbRoHandle {
    fn open_impl(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
        disable_mismatching_storage_pool_check: bool,
    ) -> Option<Self> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let inner = ffi::triedb_open(
            dbdir_path.to_str()?,
            node_lru_max_mem,
            disable_mismatching_storage_pool_check,
        );

        (!inner.is_null()).then(|| Self { inner })
    }

    pub fn open(dbdir_path: &Path, node_lru_max_mem: u64) -> Option<Self> {
        Self::open_impl(dbdir_path, node_lru_max_mem, false)
    }

    pub fn open_without_mismatching_storage_pool_check(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
    ) -> Option<Self> {
        Self::open_impl(dbdir_path, node_lru_max_mem, true)
    }

    fn inner_mut(&mut self) -> Pin<&mut ffi::TriedbRoInner> {
        self.inner.as_mut().expect("TriedbRoInner is non-null")
    }
}
