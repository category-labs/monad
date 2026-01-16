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
    ffi::{monad_event_ring, monad_event_ring_mmap, monad_event_ring_unmap},
    EventDecoder,
};

#[derive(Debug)]
pub(crate) struct RawEventRing {
    pub(crate) inner: monad_event_ring,
}

impl RawEventRing {
    pub(crate) fn mmap_from_fd(
        mmap_prot: libc::c_int,
        mmap_extra_flags: libc::c_int,
        ring_fd: libc::c_int,
        ring_offset: libc::off_t,
        error_name: &str,
    ) -> Result<Self, String> {
        monad_event_ring_mmap(
            mmap_prot,
            mmap_extra_flags,
            ring_fd,
            ring_offset,
            error_name,
        )
        .map(|inner| Self { inner })
    }

    pub(crate) fn check_type<D>(&self) -> Result<(), String>
    where
        D: EventDecoder,
    {
        D::check_ring_content_type(&self.inner)
    }
}

impl Drop for RawEventRing {
    fn drop(&mut self) {
        monad_event_ring_unmap(&mut self.inner);
    }
}

unsafe impl Send for RawEventRing {}
unsafe impl Sync for RawEventRing {}
