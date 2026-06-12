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
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>

#include <memory>

MONAD_NAMESPACE_BEGIN

void register_ethereum_state_machines()
{
    // Only OnDiskMachine participates in metadata-driven open. The
    // in-memory production path keeps the StateMachine&-passing ctor and
    // never reads from disk, so InMemoryMachine is not registered.
    mpt::register_state_machine(mpt::state_machine_kind::ethereum, [] {
        return std::unique_ptr<mpt::StateMachine>(new OnDiskMachine{});
    });
}

MONAD_NAMESPACE_END
