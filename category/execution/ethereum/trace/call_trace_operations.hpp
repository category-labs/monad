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
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/trace_traits.hpp>

#include <evmc/evmc.hpp>

namespace monad::trace::call_trace
{
    struct Enter
    {
        Enter(evmc_message const &message)
            : message{message}
        {
        }

        evmc_message const &message;
    };

    struct Exit
    {
        Exit(evmc::Result const &result)
            : result{result}
        {
        }

        evmc::Result const &result;
    };

    struct Log
    {
        Log(Receipt::Log const &log)
            : log{log}
        {
        }

        Receipt::Log const &log;
    };

    struct SelfDestruct
    {
        SelfDestruct(
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
        uint64_t const gas_used;
    };

    struct Reset
    {
    };

    using Signature = Signature<Enter, Exit, Log, SelfDestruct, Finish, Reset>;
}
