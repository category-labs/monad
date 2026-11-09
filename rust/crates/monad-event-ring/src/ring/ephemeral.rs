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

use std::os::fd::OwnedFd;

use super::{raw::RawEventRing, DecodedEventRing, EventRing, RawEventReader};
use crate::{ffi, EventDecoder, EventReader};

/// A special kind of event ring backed by an anonymous file.
///
/// This type is intended for event production local to the current process, such as testing.
#[derive(Debug)]
pub struct EphemeralEventRing<D>
where
    D: EventDecoder,
{
    ring: EventRing<D>,
    _ephemeral_fd: OwnedFd,
}

impl<D> EphemeralEventRing<D>
where
    D: EventDecoder,
{
    /// Creates a new anonymous event ring with the provided schema.
    pub fn new_with_schema(
        descriptor_shift: u8,
        payload_buf_shift: u8,
        schema_hash: &[u8; 32],
    ) -> Result<Self, String> {
        let config = ffi::monad_event_ring_simple_config {
            descriptors_shift: descriptor_shift,
            payload_buf_shift,
            context_large_pages: 0,
            content_type: D::ring_content_ctype(),
            schema_hash: schema_hash.as_ptr(),
        };
        let (inner, ephemeral_fd) =
            ffi::monad_event_ring_create_ephemeral(&config, "ephemeral event ring")?;
        Ok(Self {
            ring: EventRing::new_from_raw(RawEventRing { inner })?,
            _ephemeral_fd: ephemeral_fd,
        })
    }

    /// Provides the underlying C event-ring pointer to a scoped FFI operation.
    ///
    /// # Safety
    /// The callback must not store the pointer or use it after it returns. The caller must also
    /// ensure that the callback's operation is compatible with the event-ring content type.
    pub unsafe fn with_raw_ptr<R>(&self, callback: impl FnOnce(*mut std::ffi::c_void) -> R) -> R {
        callback(&self.ring.raw.inner as *const _ as *mut std::ffi::c_void)
    }
}

impl<D> DecodedEventRing for EphemeralEventRing<D>
where
    D: EventDecoder,
{
    type Decoder = D;

    fn create_reader<'ring>(&'ring self) -> EventReader<'ring, D> {
        let raw = RawEventReader::new(&self.ring.raw).unwrap();

        EventReader::new(raw)
    }
}
