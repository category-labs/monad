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
#include <category/execution/ethereum/trace/commands/call_trace.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json_fwd.hpp>

#include <limits>
#include <span>
#include <stack>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Transaction;

class CallTracer
{
public:
    using Signature = monad::trace::CallTraceSignature;

    CallTracer() = delete;
    CallTracer(CallTracer const &) = default;
    CallTracer(CallTracer &&) noexcept = default;
    CallTracer &operator=(CallTracer const &) = delete;
    CallTracer &operator=(CallTracer &&) noexcept = delete;
    ~CallTracer() = default;

    CallTracer(Transaction const &, std::vector<CallFrame> &);
    CallTracer(Transaction const &, std::vector<CallFrame> &, size_t max_size);

    /// Checks if the accumulated call trace size exceeds the maximum allowed
    /// size. Throws a MonadException if the size limit is exceeded.
    ///
    /// This function MUST be called by RPC methods before attempting to access
    /// the call trace.
    void check_size_limit() const;

    nlohmann::json to_json() const;

    void operator()(monad::trace::Enter const &op);

    void operator()(monad::trace::Exit const &op);

    void operator()(monad::trace::Log const &op);

    void operator()(monad::trace::SelfDestruct const &op);

    void operator()(monad::trace::Finish const &op);

    void operator()(monad::trace::CallReset const &op);

    void operator()(monad::trace::GetCallFrames const &op);

private:
    struct CallFramesStack
    {
        std::vector<CallFrame> &frames_;
        std::stack<size_t> last_{};
        std::stack<size_t> positions_{};

        explicit CallFramesStack(std::vector<CallFrame> &);

        void advance_position();

        CallFrame &top_frame();
        CallFrame &pop_frame();
        CallFrame &push_frame(CallFrame &&);
        CallFrame &push_selfdestruct_frame(CallFrame &&);

        bool has_active_frame() const;
        size_t position() const;

        void reset();
    };

    class BoundedSize
    {
        size_t const max_;
        size_t current_{0};
        bool exceeded_{false};

    public:
        explicit BoundedSize(size_t max);
        explicit operator bool() const noexcept;
        BoundedSize &operator+=(size_t additional_size) noexcept;
        void reset() noexcept;
    };

    std::vector<CallFrame> &frames_;
    CallFramesStack frames_stack_;
    Transaction const &tx_;
    BoundedSize size_;
};

MONAD_NAMESPACE_END
