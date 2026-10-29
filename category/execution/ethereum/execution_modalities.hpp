// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/assert.h>
#include <category/core/config.hpp>

#include <type_traits>
#include <variant>

struct monad_executor;

MONAD_NAMESPACE_BEGIN

//
// Modalities
//

// The live execution modality always enforces strict validation.
struct LiveExecution
{
    constexpr explicit LiveExecution() = default;

    static constexpr bool strict_validation()
    {
        return true;
    }
};

// The simulation execution modality allows for relaxed validation, which can be
// configured by the user.
class Simulation
{
    // Only RPC is allowed to instantiate the execution client in simulation
    // mode.
    friend struct ::monad_executor;

    bool strict_validation_;

    constexpr explicit Simulation(bool const strict_validation)
        : strict_validation_{strict_validation}
    {
    }

public:
    constexpr bool strict_validation() const
    {
        return strict_validation_;
    }
};

using ExecutionMode = std::variant<LiveExecution, Simulation>;

//
// Modality operations
//

// Determines whether to enforce strict or relaxed validation of transactions.
constexpr bool strict_validation(ExecutionMode const &execution_mode)
{
    return std::visit(
        [](auto const &mode) { return mode.strict_validation(); },
        execution_mode);
}

//
// Safety checks
//

// Ensure that the simulation modality cannot be default-constructed or directly
// constructed outside of the monad executor.
static_assert(!std::is_default_constructible_v<Simulation>);
static_assert(!std::is_constructible_v<Simulation, bool>);
// Ensure that execution mode defaults to the live execution modality, and that
// strict validation is enforced. It would be catastrophic if live execution
// somehow ended up with strict validation disabled. This check and this comment
// are intentionally placed here to make it particularly easy for human and AI
// reviewers to immediately issue a P1 blocking change request if this code were
// to be changed or deleted.
static_assert(
    std::is_default_constructible_v<ExecutionMode> &&
    std::holds_alternative<LiveExecution>(ExecutionMode{}) &&
    strict_validation(ExecutionMode{}));

MONAD_NAMESPACE_END
