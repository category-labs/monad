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

#include <category/mpt/config.hpp>

#include <cstdint>

MONAD_MPT_NAMESPACE_BEGIN

// Identifies which StateMachine implementation a timeline was created with.
// Persisted per-timeline in db_metadata::root_offsets_ring_t. The caller
// supplies a StateMachine to mpt::Db's constructors; the Db cross-checks
// machine->kind() against the stamped kind, and stamps it on first write
// for fresh timelines.
enum class state_machine_kind : uint8_t
{
    // sentinel; reads from a fresh (not yet stamped) timeline.
    undefined = 0,
    // OnDiskMachine / InMemoryMachine
    ethereum = 1,
    // MonadOnDiskMachine / MonadInMemoryMachine: page-encoded storage for
    // chains at MONAD_NEXT or later.
    monad = 2,
    // Future kinds extend here. Never reorder or reuse values: they are
    // persisted on disk.
};

MONAD_MPT_NAMESPACE_END
