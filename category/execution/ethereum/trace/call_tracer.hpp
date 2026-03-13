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
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>

#include <cstddef>
#include <optional>
#include <span>
#include <stack>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct Transaction;

struct CallTracerBase
{
    virtual ~CallTracerBase() = default;

    virtual void on_enter(evmc_message const &) = 0;
    virtual void on_exit(evmc::Result const &) = 0;
    virtual void on_log(size_t receipt_index, Receipt::Log) = 0;
    virtual void on_self_destruct(
        Address const &from, Address const &to,
        uint256_t const &transferred_balance) = 0;
    virtual void on_finish(uint64_t const) = 0;
    virtual void reset() = 0;
    virtual std::span<CallFrame const> get_call_frames() const = 0;
};

struct NoopCallTracer final : public CallTracerBase
{
    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void on_log(size_t, Receipt::Log) override;
    virtual void on_self_destruct(
        Address const &, Address const &, uint256_t const &) override;
    virtual void on_finish(uint64_t const) override;
    virtual void reset() override;
    virtual std::span<CallFrame const> get_call_frames() const override;
};

class CallTracer final : public CallTracerBase
{
    std::vector<CallFrame> &frames_;
    std::stack<size_t> last_{};
    std::stack<size_t> positions_{};
    Transaction const &tx_;

public:
    CallTracer() = delete;
    CallTracer(CallTracer const &) = delete;
    CallTracer(CallTracer &&) = delete;
    CallTracer(Transaction const &, std::vector<CallFrame> &);

    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void on_log(size_t receipt_index, Receipt::Log) override;
    virtual void on_self_destruct(
        Address const &from, Address const &to,
        uint256_t const &transferred_balance) override;
    virtual void on_finish(uint64_t const) override;
    virtual void reset() override;
    virtual std::span<CallFrame const> get_call_frames() const override;

    nlohmann::json to_json() const;
};

MONAD_NAMESPACE_END
