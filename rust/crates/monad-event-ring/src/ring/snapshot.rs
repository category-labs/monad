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

use super::{raw::RawEventRing, DecodedEventRing, EventRing, RawEventReader};
use crate::{ffi, EventDecoder, EventReader, EventRingPath};

/// A special kind of event ring mapped to a static file for replaying events.
///
/// This type is intended to be used for testing / recovery where, during normal operation, an
/// [`EventRing`] would be used.
#[derive(Debug)]
pub struct SnapshotEventRing<D>
where
    D: EventDecoder,
{
    ring: EventRing<D>,
    snapshot_fd: libc::c_int,
}

impl<D> SnapshotEventRing<D>
where
    D: EventDecoder,
{
    /// Produces an event ring by decoding the file at the provided input path, which is expected to
    /// be a snapshot file (a single zstd-compressed frame containing an event ring).
    ///
    /// Internally, this function writes the decoded bytes to an anonymous file which is destroyed
    /// when the [`SnapshotEventRing`] is dropped.
    pub fn new_from_zstd_path(
        path: impl AsRef<EventRingPath>,
        max_size: Option<usize>,
    ) -> Result<Self, String> {
        let file = path.as_ref().open().map_err(|err| err.to_string())?;

        let error_name = path.as_ref().as_error_name();

        let Some(decompressed_file) =
            ffi::monad_event_decompress_snapshot_fd(&file, max_size, &error_name)?
        else {
            return Err(format!("{error_name} is not an event ring snapshot"));
        };

        Self::new_from_decompressed_file(decompressed_file, &error_name)
    }

    /// Produces an event ring by decoding the provided `bytes` input, which is expected to contain
    /// a snapshot file (a single zstd-compressed frame containing an event ring).
    ///
    /// Internally, this function writes the decoded bytes to an anonymous file which is destroyed
    /// when the [`SnapshotEventRing`] is dropped.
    pub fn new_from_zstd_bytes(
        name: impl AsRef<str>,
        zstd_bytes: &[u8],
        max_size: Option<usize>,
    ) -> Result<Self, String> {
        let name = name.as_ref();

        let Some(decompressed_file) =
            ffi::monad_event_decompress_snapshot_mem(zstd_bytes, max_size, name)?
        else {
            return Err(format!("{name} is not an event ring snapshot"));
        };

        Self::new_from_decompressed_file(decompressed_file, name)
    }

    fn new_from_decompressed_file(
        file: std::fs::File,
        name: impl AsRef<str>,
    ) -> Result<Self, String> {
        use std::os::fd::{AsRawFd, IntoRawFd};

        let snapshot_off: libc::off_t = 0;

        let raw = RawEventRing::mmap_from_fd(
            libc::PROT_READ,
            0,
            file.as_raw_fd(),
            snapshot_off,
            name.as_ref(),
        )?;

        Ok(Self {
            ring: EventRing::new_from_raw(raw)?,
            snapshot_fd: file.into_raw_fd(),
        })
    }
}

impl<D> Drop for SnapshotEventRing<D>
where
    D: EventDecoder,
{
    fn drop(&mut self) {
        let ret = unsafe { libc::close(self.snapshot_fd) };
        assert_eq!(ret, 0);
    }
}

impl<D> DecodedEventRing for SnapshotEventRing<D>
where
    D: EventDecoder,
{
    type Decoder = D;

    fn create_reader<'ring>(&'ring self) -> EventReader<'ring, D> {
        let raw = RawEventReader::new(&self.ring.raw).unwrap();

        EventReader::new_snapshot(raw)
    }
}
