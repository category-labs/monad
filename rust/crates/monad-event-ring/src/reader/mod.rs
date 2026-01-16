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

pub(crate) use self::raw::RawEventReader;
use crate::{ffi::monad_event_iterator_reset, EventDecoder, EventDescriptor, EventNextResult};

mod raw;

/// Used to consume events from an [`EventRing`](crate::EventRing).
pub struct EventReader<'ring, D>
where
    D: EventDecoder,
{
    pub(crate) raw: RawEventReader<'ring>,
    _phantom: PhantomData<D>,
}

impl<'ring, D> EventReader<'ring, D>
where
    D: EventDecoder,
{
    pub(crate) fn new(raw: RawEventReader<'ring>) -> Self {
        Self {
            raw,
            _phantom: PhantomData,
        }
    }

    pub(crate) fn new_snapshot(mut raw: RawEventReader<'ring>) -> Self {
        raw.inner.read_last_seqno = 0;

        Self {
            raw,
            _phantom: PhantomData,
        }
    }

    /// Produces the next event in the ring.
    pub fn next_descriptor(&mut self) -> EventNextResult<EventDescriptor<'ring, D>> {
        self.raw.next_descriptor().map(EventDescriptor::new)
    }

    /// Resets the reader to the latest event in the ring.
    pub fn reset(&mut self) {
        monad_event_iterator_reset(&mut self.raw.inner);
    }
}
