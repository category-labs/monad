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
    ffi::{monad_event_ring_iter, monad_event_ring_iterator_init},
    ring::RawEventRing,
    EventNextResult, RawEventDescriptor,
};

#[derive(Debug)]
pub(crate) struct RawEventReader<'ring> {
    pub(crate) inner: monad_event_ring_iter,
    pub(crate) event_ring: &'ring RawEventRing,
}

impl<'ring> RawEventReader<'ring> {
    pub(crate) fn new(event_ring: &'ring RawEventRing) -> Result<Self, String> {
        let inner = monad_event_ring_iterator_init(&event_ring.inner)?;

        Ok(Self { inner, event_ring })
    }

    pub(crate) fn next_descriptor(&mut self) -> EventNextResult<RawEventDescriptor<'ring>> {
        EventNextResult::new_from_raw(self)
    }
}

unsafe impl<'ring> Send for RawEventReader<'ring> {}
