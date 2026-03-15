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

use std::marker::PhantomData;

pub(crate) use self::raw::RawEventRing;
pub use self::snapshot::SnapshotEventRing;
use crate::{EventDecoder, EventReader, EventRingPath, RawEventReader};

mod raw;
mod snapshot;

/// A unified interface for event rings.
pub trait DecodedEventRing {
    /// The decoder used to read events from this event ring.
    type Decoder: EventDecoder;

    /// Produces a reader that produces events from this ring.
    fn create_reader<'ring>(&'ring self) -> EventReader<'ring, Self::Decoder>;
}

/// An event ring created from a file.
pub struct EventRing<D>
where
    D: EventDecoder,
{
    raw: RawEventRing,
    _phantom: PhantomData<D>,
}

impl<D> std::fmt::Debug for EventRing<D>
where
    D: EventDecoder,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EventRing")
            .field("raw", &self.raw)
            .field("type", &D::ring_content_ctype())
            .finish()
    }
}

impl<D> EventRing<D>
where
    D: EventDecoder,
{
    /// Synchronously creates a new event ring from the provided path.
    pub fn new(path: impl AsRef<EventRingPath>) -> Result<Self, String> {
        use std::os::fd::AsRawFd;

        let file = path.as_ref().open().map_err(|err| err.to_string())?;

        let raw = RawEventRing::mmap_from_fd(
            libc::PROT_READ,
            #[cfg(target_os = "linux")]
            libc::MAP_POPULATE,
            #[cfg(not(target_os = "linux"))]
            0,
            file.as_raw_fd(),
            0,
            &path.as_ref().as_error_name(),
        )?;

        Self::new_from_raw(raw)
    }

    pub(crate) fn new_from_raw(raw: RawEventRing) -> Result<Self, String> {
        raw.check_type::<D>()?;

        Ok(Self {
            raw,
            _phantom: PhantomData,
        })
    }
}

impl<D> DecodedEventRing for EventRing<D>
where
    D: EventDecoder,
{
    type Decoder = D;

    fn create_reader<'ring>(&'ring self) -> EventReader<'ring, Self::Decoder> {
        let raw = RawEventReader::new(&self.raw).unwrap();

        EventReader::new(raw)
    }
}
