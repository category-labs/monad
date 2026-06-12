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
#include <category/mpt/state_machine.hpp>

#include <cstdint>
#include <functional>
#include <memory>

MONAD_MPT_NAMESPACE_BEGIN

// Identifies which StateMachine implementation a timeline was created with.
// Persisted per-timeline in db_metadata::root_offsets_ring_t so that opens
// reconstruct the right SM via the registry below.
enum class state_machine_kind : uint8_t
{
    // OnDiskMachine; registered by register_ethereum_state_machines. Value 0
    // so a zeroed metadata byte (DBs created before the kind was persisted,
    // freshly-created pools) reads back as ethereum with no migration step.
    ethereum = 0,
    // Future kinds (e.g. the dual-timeline hash migration target) extend here.
    // Never reorder or reuse values: they are persisted on disk.
};

constexpr uint8_t NUM_STATE_MACHINE_KINDS = 8;

using state_machine_factory = std::function<std::unique_ptr<StateMachine>()>;

// Register a factory for a given kind. The mpt module never knows about
// concrete StateMachine subclasses; external init code (e.g.
// register_ethereum_state_machines() in execution/ethereum/db) populates
// the registry at process start before any mpt::Db is constructed.
//
// Idempotent: re-registering the same kind overwrites the previous factory.
void register_state_machine(state_machine_kind, state_machine_factory);

// Construct a StateMachine for the given kind via the registered factory.
// Aborts (MONAD_ASSERT) if the kind is out of range or has no registered
// factory.
std::unique_ptr<StateMachine> create_state_machine(state_machine_kind);

MONAD_MPT_NAMESPACE_END
