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
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

class State;

namespace trace
{
    struct Enter
    {
        explicit Enter(evmc_message const &message)
            : message{message}
        {
        }

        evmc_message const &message;
    };

    struct Exit
    {
        explicit Exit(evmc::Result const &result)
            : result{result}
        {
        }

        evmc::Result const &result;
    };

    struct Log
    {
        explicit Log(Receipt::Log const &log)
            : log{log}
        {
        }

        Receipt::Log const &log;
    };

    struct SelfDestruct
    {
        explicit SelfDestruct(
            Address const &from, Address const &to,
            uint256_t const &transferred_balance)
            : from{from}
            , to{to}
            , transferred_balance{transferred_balance}
        {
        }

        Address const &from;
        Address const &to;
        uint256_t const &transferred_balance;
    };

    struct Finish
    {
        explicit Finish(uint64_t const gas_used)
            : gas_used{gas_used}
        {
        }

        uint64_t const gas_used;
    };

    struct GetCallFrames
    {
        explicit GetCallFrames(std::span<CallFrame const> *call_frames)
            : call_frames{call_frames}
        {
        }

        std::span<CallFrame const> *call_frames;
    };

    struct NativeTransfer
    {
        explicit NativeTransfer(
            State &state, Address const &system, Address const &from,
            Address const &to, uint256_t const &transferred_balance)
            : state{state}
            , transferred_balance{transferred_balance}
            , system{system}
            , from{from}
            , to{to}
        {
        }

        State &state;
        uint256_t const &transferred_balance;
        Address const &system;
        Address const &from;
        Address const &to;
    };

    using CallTraceSignature = monad::Signature<
        Enter, Exit, Log, SelfDestruct, Finish, GetCallFrames, NativeTransfer>;
}

MONAD_NAMESPACE_END
