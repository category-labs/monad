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

#include <category/core/config.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <optional>
#include <span>
#include <stack>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Receipt;
struct Transaction;

struct CallTracerBase
{
    virtual void on_enter(evmc_message const &) = 0;
    virtual void on_exit(evmc::Result const &) = 0;
    virtual void on_self_destruct(Address const &from, Address const &to) = 0;
    virtual void on_finish(uint64_t const) = 0;
    virtual std::vector<CallFrame> &&get_frames() && = 0;

    virtual ~CallTracerBase() = default;
};

struct NoopCallTracer final : public CallTracerBase
{
    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void on_self_destruct(Address const &, Address const &) override;
    virtual void on_finish(uint64_t const) override;
    virtual std::vector<CallFrame> &&get_frames() && override;

private:
    std::vector<CallFrame> frames_{};
};

class CallTracer final : public CallTracerBase
{
    std::vector<CallFrame> frames_;
    std::stack<size_t> last_;
    uint64_t depth_;
    Transaction const &tx_;

public:
    CallTracer() = delete;
    CallTracer(CallTracer const &) = delete;
    CallTracer(CallTracer &&) = delete;
    explicit CallTracer(Transaction const &);

    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void
    on_self_destruct(Address const &from, Address const &to) override;
    virtual void on_finish(uint64_t const) override;
    virtual std::vector<CallFrame> &&get_frames() && override;

    nlohmann::json to_json() const;
};

void enable_call_tracing(bool const enabled);
std::unique_ptr<CallTracerBase> create_call_tracer(Transaction const &tx);

MONAD_NAMESPACE_END
