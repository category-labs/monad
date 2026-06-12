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

#include <category/core/assert.h>
#include <category/mpt/config.hpp>
#include <category/mpt/state_machine.hpp>
#include <category/mpt/state_machine_kind.hpp>

#include <array>
#include <cstdint>
#include <memory>
#include <utility>

MONAD_MPT_NAMESPACE_BEGIN

namespace
{
    std::array<state_machine_factory, NUM_STATE_MACHINE_KINDS> &registry()
    {
        static std::array<state_machine_factory, NUM_STATE_MACHINE_KINDS> r{};
        return r;
    }
}

void register_state_machine(
    state_machine_kind const kind, state_machine_factory factory)
{
    auto const i = static_cast<uint8_t>(kind);
    MONAD_ASSERT(i < NUM_STATE_MACHINE_KINDS);
    registry()[i] = std::move(factory);
}

std::unique_ptr<StateMachine>
create_state_machine(state_machine_kind const kind)
{
    auto const i = static_cast<uint8_t>(kind);
    MONAD_ASSERT(i < NUM_STATE_MACHINE_KINDS);
    auto const &factory = registry()[i];
    // Aborts here mean external init (register_ethereum_state_machines or
    // similar) didn't run before mpt::Db tried to construct a SM, or the
    // on-disk kind names a SM no longer compiled in.
    MONAD_ASSERT(static_cast<bool>(factory));
    return factory();
}

MONAD_MPT_NAMESPACE_END
