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

#pragma once

#include <category/core/config.hpp>
#include <category/core/event/event_ring.h>

#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

/// An RAII helper class for exclusive writers to event rings; it is assumed
/// that the ring_fd file descriptor passed into this object will be owned by
/// it (i.e., will be closed by this class' destructor, and not by the caller).
/// This is so an instance of this class can hold open a BSD-style advisory
/// exclusive file lock (see flock(2)) which marks the event ring as "owned";
/// another aspect of the "ownership" contract is that the destructor of this
/// class will also unlink the file at `ring_path` from the filesystem
class OwnedEventRing
{
public:
    explicit OwnedEventRing(
        int ring_fd, std::string_view ring_path, monad_event_ring const &);

    OwnedEventRing(OwnedEventRing const &) = delete;
    OwnedEventRing(OwnedEventRing &&) = delete;

    ~OwnedEventRing();

    monad_event_ring const *get_event_ring() const
    {
        return &event_ring_;
    }

private:
    monad_event_ring event_ring_;
    std::string ring_path_;
    int ring_fd_;
};

MONAD_NAMESPACE_END
