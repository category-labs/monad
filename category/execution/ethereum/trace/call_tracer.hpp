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

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_trace_operations.hpp>

#include <evmc/evmc.hpp>

#include <span>
#include <stack>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Transaction;

struct CallTraceRunner
{
    using Signature = monad::trace::call_trace::Signature;

    CallTraceRunner(Transaction const &, std::vector<CallFrame> &);

    void operator()(monad::trace::call_trace::Enter const &);
    void operator()(monad::trace::call_trace::Exit const &);
    void operator()(monad::trace::call_trace::Log const &);
    void operator()(monad::trace::call_trace::SelfDestruct const &);
    void operator()(monad::trace::call_trace::Finish const &);
    void operator()(monad::trace::call_trace::Reset const &);
    void operator()(monad::trace::call_trace::GetCallFrames const &);

private:
    std::vector<CallFrame> &frames_;
    std::stack<size_t> last_{};
    std::stack<size_t> positions_{};
    Transaction const &tx_;
};

MONAD_NAMESPACE_END
