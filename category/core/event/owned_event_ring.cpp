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

#include <category/core/config.hpp>
#include <category/core/event/event_ring.h>
#include <category/core/event/owned_event_ring.hpp>

#include <string_view>

#include <unistd.h>

MONAD_NAMESPACE_BEGIN

OwnedEventRing::OwnedEventRing(
    int ring_fd, std::string_view ring_path, monad_event_ring const &event_ring)
    : event_ring_{event_ring}
    , ring_path_{ring_path}
    , ring_fd_{ring_fd}
{
}

OwnedEventRing::~OwnedEventRing()
{
    // Check if we have a path before trying to unlink it; the path will be
    // empty in the memfd_create(2) case
    if (!ring_path_.empty()) {
        (void)unlink(ring_path_.c_str());
    }
    (void)close(ring_fd_);
    monad_event_ring_unmap(&event_ring_);
}

MONAD_NAMESPACE_END
