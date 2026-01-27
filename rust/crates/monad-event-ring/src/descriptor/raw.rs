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

use crate::{
    ffi::{monad_event_descriptor, monad_event_ring_payload_check, monad_event_ring_payload_peek},
    EventPayloadResult, RawEventRing,
};

#[derive(Debug)]
pub(crate) struct RawEventDescriptor<'ring> {
    inner: monad_event_descriptor,
    ring: &'ring RawEventRing,
}

impl<'ring> RawEventDescriptor<'ring> {
    pub(crate) fn new(
        ring: &'ring RawEventRing,
        c_event_descriptor: monad_event_descriptor,
    ) -> Self {
        Self {
            inner: c_event_descriptor,
            ring,
        }
    }

    pub(crate) fn try_filter_map<T>(
        &self,
        f: impl FnOnce(RawEventDescriptorInfo, &[u8]) -> T,
    ) -> EventPayloadResult<T> {
        let Some(bytes) = monad_event_ring_payload_peek(&self.ring.inner, &self.inner) else {
            return EventPayloadResult::Expired;
        };

        let value = f(
            RawEventDescriptorInfo {
                seqno: self.inner.seqno,
                event_type: self.inner.event_type,
                content_ext: self.inner.content_ext,
            },
            bytes,
        );

        if monad_event_ring_payload_check(&self.ring.inner, &self.inner) {
            EventPayloadResult::Ready(value)
        } else {
            EventPayloadResult::Expired
        }
    }
}

pub(crate) struct RawEventDescriptorInfo {
    pub seqno: u64,

    pub event_type: u16,

    pub content_ext: [u64; 4],
}
