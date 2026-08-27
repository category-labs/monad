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
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/commands/call_trace.hpp>

#include <evmc/evmc.hpp>

#include <cstdint>
#include <limits>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Transaction;

struct CallTracer
{
    using Signature = monad::trace::CallTraceSignature;

    explicit CallTracer(Transaction const &, std::vector<CallFrame> &) {}

    explicit CallTracer(
        Transaction const &, std::vector<CallFrame> &, size_t const)
    {
    }

    void check_size_limit() const noexcept {}

    void operator()(monad::trace::Enter const &op)
    {
        (void)op;
    }

    void operator()(monad::trace::Exit const &op)
    {
        (void)op;
    }

    void operator()(monad::trace::Log const &op)
    {
        (void)op;
    }

    void operator()(monad::trace::SelfDestruct const &op)
    {
        (void)op;
    }

    void operator()(monad::trace::Finish const &op)
    {
        (void)op;
    }

    void operator()(monad::trace::CallReset const &op)
    {
        (void)op;
    }

    void operator()(monad::trace::GetCallFrames const &op)
    {
        *op.call_frames = std::span<CallFrame const>{};
    }

    void operator()(monad::trace::NativeTransfer const &op)
    {
        (void)op;
    }
};

MONAD_NAMESPACE_END
