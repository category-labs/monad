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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>
#include <category/vm/code.hpp>

MONAD_NAMESPACE_BEGIN
class State;
struct bytes32_t;
MONAD_NAMESPACE_END

namespace monad::trace::state_trace
{
    struct State
    {
        monad::State &state;

        State(monad::State &state)
            : state{state}
        {
        }
    };

    struct RejectFrame
    {
        monad::State const &state;

        RejectFrame(monad::State const &state)
            : state{state}
        {
        }
    };

    struct Reset
    {
    };

    struct MaybeReadCode
    {
        using return_type = bool;
        monad::State &state;
        monad::Address address;

        MaybeReadCode(monad::State &state, monad::Address const &address)
            : state{state}
            , address{address}
        {
        }
    };

    struct ReadCode
    {
        monad::bytes32_t const &code_hash;
        monad::vm::SharedIntercode const &code;

        ReadCode(
            monad::bytes32_t const &code_hash,
            monad::vm::SharedIntercode const &code)
            : code_hash{code_hash}
            , code{code}
        {
        }
    };
}
