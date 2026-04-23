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

use std::{cell::UnsafeCell, path::Path, pin::Pin};

use cxx::UniquePtr;
use futures::channel::oneshot::Sender;

use self::ffi::OpaqueContext;
pub use self::ffi::UpsertEntry;

mod ffi;

pub type AsyncReadSender = Sender<Option<Box<[u8]>>>;

/// Layout-compatible with `monad::bytes32_t` / `evmc::bytes32`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Bytes32(pub [u8; 32]);

unsafe impl cxx::ExternType for Bytes32 {
    type Id = cxx::type_id!("monad::bytes32_t");
    type Kind = cxx::kind::Trivial;
}

/// Layout-compatible with `monad::staking::Validator` (33 + 48 + 32).
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct Validator {
    pub secp_pubkey: [u8; 33],
    pub bls_pubkey: [u8; 48],
    pub stake: [u8; 32],
}

unsafe impl cxx::ExternType for Validator {
    type Id = cxx::type_id!("monad::staking::Validator");
    type Kind = cxx::kind::Trivial;
}

/// Borrowed view of a nibble-aligned key.
///
/// Odd nibble lengths are supported — the trailing low nibble of the last
/// byte is ignored when `nibble_len` is odd.
#[derive(Debug, Clone, Copy)]
pub struct NibblesView<'a> {
    bytes: &'a [u8],
    nibble_len: u8,
}

impl<'a> NibblesView<'a> {
    /// Returns `None` if `bytes` is shorter than `ceil(nibble_len / 2)`.
    pub fn new(bytes: &'a [u8], nibble_len: u8) -> Option<Self> {
        ((nibble_len as usize).div_ceil(2) <= bytes.len()).then_some(Self { bytes, nibble_len })
    }

    /// Interprets the full slice as a byte-aligned key. Returns `None` if
    /// the slice is longer than 127 bytes (would overflow `u8` nibbles).
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

#[derive(Debug, Clone)]
pub struct TraverseEntry {
    pub key: Box<[u8]>,
    pub value: Box<[u8]>,
}

/// A value read from the triedb, holding a cursor that pins the underlying
/// node in the cache. The byte view is valid as long as the `NodeValue` is
/// alive.
pub struct NodeValue {
    cursor: UniquePtr<ffi::NodeCursor>,
}

impl NodeValue {
    fn new(cursor: UniquePtr<ffi::NodeCursor>) -> Option<Self> {
        (!cursor.is_null()).then_some(Self { cursor })
    }

    fn cursor(&self) -> &ffi::NodeCursor {
        unsafe { self.cursor.as_ref().unwrap() }
    }

    pub fn bytes(&self) -> &[u8] {
        ffi::node_cursor_value(self.cursor())
    }

    pub fn into_boxed_slice(self) -> Box<[u8]> {
        self.bytes().into()
    }
}

impl std::fmt::Debug for NodeValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeValue")
            .field("bytes", &self.bytes())
            .finish()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum OpenError {
    NonUtf8Path,
    /// Diagnostics are emitted to the C++ log.
    OpenFailed,
}

impl std::fmt::Display for OpenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NonUtf8Path => f.write_str("triedb path is not valid UTF-8"),
            Self::OpenFailed => f.write_str("failed to open triedb; see C++ logs"),
        }
    }
}

impl std::error::Error for OpenError {}

/// Read-only triedb handle. Not `Send`.
pub struct TriedbRoHandle {
    inner: UniquePtr<ffi::TriedbRoInner>,
}

/// Read-write triedb handle. Not `Send`.
pub struct TriedbRwHandle {
    inner: UniquePtr<ffi::TriedbRwInner>,
}

impl std::fmt::Debug for TriedbRoHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TriedbRoHandle").finish_non_exhaustive()
    }
}

impl std::fmt::Debug for TriedbRwHandle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TriedbRwHandle").finish_non_exhaustive()
    }
}

/// Read operations available on both [`TriedbRoHandle`] and [`TriedbRwHandle`].
///
/// Metadata getters return `None` when not recorded (`u64::MAX` /
/// all-zeros sentinel).
pub trait Triedb {
    /// Returns `None` if the key is absent.
    fn find(&self, key: NibblesView<'_>, block_id: u64) -> Option<NodeValue>;

    fn latest_proposed_block(&self) -> Option<u64>;

    /// May return an inconsistent id under concurrent writes.
    fn latest_proposed_block_id(&self) -> Option<[u8; 32]>;

    fn latest_voted_block(&self) -> Option<u64>;

    /// May return an inconsistent id under concurrent writes.
    fn latest_voted_block_id(&self) -> Option<[u8; 32]>;

    fn latest_finalized_block(&self) -> Option<u64>;

    fn latest_verified_block(&self) -> Option<u64>;

    fn earliest_finalized_block(&self) -> Option<u64>;

    /// The highest version present in the DB, regardless of finalization.
    fn latest_version(&self) -> Option<u64>;
}

macro_rules! impl_triedb {
    ($handle:ty, $prefix:ident) => {
        paste::paste! {
            impl Triedb for $handle {
                fn find(&self, key: NibblesView<'_>, block_id: u64) -> Option<NodeValue> {
                    NodeValue::new(ffi::[<$prefix _find>](
                        &self.inner, key.bytes, key.nibble_len, block_id,
                    ))
                }

                #[inline]
                fn latest_proposed_block(&self) -> Option<u64> {
                    parse_block_num(ffi::[<$prefix _latest_proposed_version>](&self.inner))
                }

                #[inline]
                fn latest_voted_block(&self) -> Option<u64> {
                    parse_block_num(ffi::[<$prefix _latest_voted_version>](&self.inner))
                }

                #[inline]
                fn latest_finalized_block(&self) -> Option<u64> {
                    parse_block_num(ffi::[<$prefix _latest_finalized_version>](&self.inner))
                }

                #[inline]
                fn latest_verified_block(&self) -> Option<u64> {
                    parse_block_num(ffi::[<$prefix _latest_verified_version>](&self.inner))
                }

                #[inline]
                fn earliest_finalized_block(&self) -> Option<u64> {
                    parse_block_num(ffi::[<$prefix _earliest_version>](&self.inner))
                }

                #[inline]
                fn latest_version(&self) -> Option<u64> {
                    parse_block_num(ffi::[<$prefix _latest_version>](&self.inner))
                }

                #[inline]
                fn latest_proposed_block_id(&self) -> Option<[u8; 32]> {
                    parse_block_id(ffi::[<$prefix _latest_proposed_block_id>](&self.inner))
                }

                #[inline]
                fn latest_voted_block_id(&self) -> Option<[u8; 32]> {
                    parse_block_id(ffi::[<$prefix _latest_voted_block_id>](&self.inner))
                }
            }
        }
    };
}

impl_triedb!(TriedbRoHandle, triedb_ro);
impl_triedb!(TriedbRwHandle, triedb_rw);

impl TriedbRoHandle {
    /// Open in read-only mode. `dbdir_path` may be a single block device
    /// or a directory containing block devices.
    ///
    /// `disable_mismatching_storage_pool_check = true` bypasses the storage
    /// pool configuration-hash check, allowing opens against databases
    /// whose inode changed (e.g. after copying between filesystems).
    /// Use with caution: it can mask genuine corruption.
    pub fn open(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
        disable_mismatching_storage_pool_check: bool,
    ) -> Result<Self, OpenError> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let path_str = dbdir_path.to_str().ok_or(OpenError::NonUtf8Path)?;
        let inner = ffi::triedb_open(
            path_str,
            node_lru_max_mem,
            disable_mismatching_storage_pool_check,
        );
        if inner.is_null() {
            return Err(OpenError::OpenFailed);
        }
        Ok(Self { inner })
    }

    pub fn find_async(&mut self, key: NibblesView<'_>, block_id: u64, sender: AsyncReadSender) {
        let ctx = Box::into_raw(Box::new(sender)) as *mut OpaqueContext;
        unsafe {
            ffi::triedb_async_read(self.inner_mut(), key.bytes, key.nibble_len, block_id, ctx)
        };
    }

    pub fn traverse_blocking(
        &mut self,
        key: NibblesView<'_>,
        block_id: u64,
        sender: TraverseSender,
    ) {
        let ctx = Box::into_raw(Box::new(TraverseContext::new(sender))) as *mut OpaqueContext;
        let completed = unsafe {
            ffi::triedb_traverse_sync(self.inner_mut(), key.bytes, key.nibble_len, block_id, ctx)
        };
        unsafe { traverse_finished_callback(ctx, completed) };
    }

    pub fn traverse(&mut self, key: NibblesView<'_>, block_id: u64, sender: TraverseSender) {
        let ctx = Box::into_raw(Box::new(TraverseContext::new(sender))) as *mut OpaqueContext;
        unsafe {
            ffi::triedb_async_traverse(self.inner_mut(), key.bytes, key.nibble_len, block_id, ctx)
        };
    }

    /// Yields every leaf under `prefix` whose full key lies in `[min, max)`.
    pub fn traverse_range(
        &mut self,
        prefix: NibblesView<'_>,
        min: NibblesView<'_>,
        max: NibblesView<'_>,
        block_id: u64,
        sender: TraverseSender,
    ) {
        let ctx = Box::into_raw(Box::new(TraverseContext::new(sender))) as *mut OpaqueContext;
        unsafe {
            ffi::triedb_async_ranged_get(
                self.inner_mut(),
                prefix.bytes,
                prefix.nibble_len,
                min.bytes,
                min.nibble_len,
                max.bytes,
                max.nibble_len,
                block_id,
                ctx,
            );
        }
    }

    /// If `blocking`, sleeps until at least one completion is available.
    pub fn poll(&mut self, blocking: bool, max_completions: usize) -> usize {
        ffi::triedb_poll(self.inner_mut(), blocking, max_completions)
    }

    /// `None` means no valset is stored (distinct from an empty set).
    pub fn validator_set_at_block(
        &mut self,
        block_num: usize,
        requested_epoch: u64,
    ) -> Option<Vec<Validator>> {
        let mut found = false;
        let valset =
            ffi::triedb_read_valset(self.inner_mut(), block_num, requested_epoch, &mut found);
        found.then_some(valset)
    }

    fn inner_mut(&mut self) -> Pin<&mut ffi::TriedbRoInner> {
        self.inner
            .as_mut()
            .expect("TriedbRoInner is never null after construction")
    }
}

impl TriedbRwHandle {
    /// Open a new read-write triedb backed by an anonymous in-memory inode.
    /// Intended for tests and benchmarks.
    pub fn open_rw_memory(
        node_lru_max_mem: u64,
        file_size_gb: i64,
        compaction: bool,
    ) -> Result<Self, OpenError> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let inner = ffi::triedb_open_rw_memory(node_lru_max_mem, file_size_gb, compaction);
        if inner.is_null() {
            return Err(OpenError::OpenFailed);
        }
        Ok(Self { inner })
    }

    /// Create a new read-write triedb, truncating any existing file at
    /// `dbdir_path` to `file_size_gb` GiB.
    pub fn create(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
        file_size_gb: i64,
        compaction: bool,
    ) -> Result<Self, OpenError> {
        Self::open_rw_impl(
            dbdir_path,
            false,
            node_lru_max_mem,
            file_size_gb,
            compaction,
        )
    }

    /// Open an existing read-write triedb at `dbdir_path`, preserving its
    /// contents. `file_size_gb` is used only if the file does not yet
    /// exist (it won't, normally, for `open_rw`) — the storage pool
    /// skips ftruncate on existing files.
    pub fn open_rw(
        dbdir_path: &Path,
        node_lru_max_mem: u64,
        file_size_gb: i64,
        compaction: bool,
    ) -> Result<Self, OpenError> {
        Self::open_rw_impl(dbdir_path, true, node_lru_max_mem, file_size_gb, compaction)
    }

    fn open_rw_impl(
        dbdir_path: &Path,
        append: bool,
        node_lru_max_mem: u64,
        file_size_gb: i64,
        compaction: bool,
    ) -> Result<Self, OpenError> {
        monad_cxx::init_cxx_logging(tracing::Level::WARN);

        let path_str = dbdir_path.to_str().ok_or(OpenError::NonUtf8Path)?;
        let inner =
            ffi::triedb_open_rw(path_str, append, node_lru_max_mem, file_size_gb, compaction);
        if inner.is_null() {
            return Err(OpenError::OpenFailed);
        }
        Ok(Self { inner })
    }

    /// Apply a batch of upserts at `block_id`, advancing the current root.
    pub fn upsert(&mut self, updates: &[UpsertEntry], block_id: u64) {
        ffi::triedb_upsert(self.inner_mut(), updates, block_id);
    }

    /// Reset the cached root so the next upsert starts from an empty trie.
    pub fn clear_root(&mut self) {
        ffi::triedb_clear_root(self.inner_mut());
    }

    /// Load the root for `version` into the cache. Returns `false` if no
    /// such version exists on disk.
    pub fn load_root(&mut self, version: u64) -> bool {
        ffi::triedb_load_root(self.inner_mut(), version)
    }

    pub fn update_finalized_version(&mut self, version: u64) {
        ffi::triedb_update_finalized_version(self.inner_mut(), version);
    }

    pub fn update_voted_metadata(&mut self, version: u64, block_id: [u8; 32]) {
        ffi::triedb_update_voted_metadata(self.inner_mut(), version, &Bytes32(block_id));
    }

    pub fn update_proposed_metadata(&mut self, version: u64, block_id: [u8; 32]) {
        ffi::triedb_update_proposed_metadata(self.inner_mut(), version, &Bytes32(block_id));
    }

    fn inner_mut(&mut self) -> Pin<&mut ffi::TriedbRwInner> {
        self.inner
            .as_mut()
            .expect("TriedbRwInner is never null after construction")
    }
}

#[inline]
fn parse_block_num(value: u64) -> Option<u64> {
    (value != u64::MAX).then_some(value)
}

#[inline]
fn parse_block_id(value: Bytes32) -> Option<[u8; 32]> {
    (value.0 != [0u8; 32]).then_some(value.0)
}

pub type TraverseSender = Sender<Option<Box<[TraverseEntry]>>>;

struct TraverseContext {
    data: UnsafeCell<Vec<TraverseEntry>>,
    sender: TraverseSender,
}

impl TraverseContext {
    fn new(sender: TraverseSender) -> Self {
        Self {
            data: UnsafeCell::new(Vec::new()),
            sender,
        }
    }
}

unsafe fn async_read_on_complete(ctx: *mut OpaqueContext, value: &[u8], found: bool) {
    let sender = unsafe { *Box::from_raw(ctx as *mut AsyncReadSender) };
    let _ = sender.send(found.then(|| value.into()));
}

unsafe fn traverse_value_callback(ctx: *mut OpaqueContext, key: &[u8], value: &[u8]) {
    let ctx = unsafe { &*(ctx as *const TraverseContext) };
    unsafe { &mut *ctx.data.get() }.push(TraverseEntry {
        key: key.into(),
        value: value.into(),
    });
}

unsafe fn traverse_finished_callback(ctx: *mut OpaqueContext, completed: bool) {
    let ctx = unsafe { Box::from_raw(ctx as *mut TraverseContext) };
    let data = std::mem::take(unsafe { &mut *ctx.data.get() });
    let _ = ctx
        .sender
        .send(completed.then_some(data.into_boxed_slice()));
}
