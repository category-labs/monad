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

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/contract/abi_encode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/events.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <optional>
#include <span>
#include <stack>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

CallTraceRunner::CallTraceRunner(
    Transaction const &tx, std::vector<CallFrame> &frames)
    : CallTraceRunner(tx, frames, false)
{
}

CallTraceRunner::CallTraceRunner(
    Transaction const &tx, std::vector<CallFrame> &frames,
    bool log_native_transfers)
    : frames_(frames)
    , tx_(tx)
    , log_native_transfers_(log_native_transfers)
{
    frames_.reserve(128);
    positions_.push(0);
}

void CallTraceRunner::operator()(monad::trace::call_trace::Enter const &op)
{
    auto const &msg = op.message;

    MONAD_ASSERT(!positions_.empty());

    positions_.top()++;
    positions_.push(0);

    auto const depth = static_cast<uint64_t>(msg.depth);

    // This is to conform with quicknode RPC
    Address const from =
        msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE
            ? msg.recipient
            : msg.sender;

    std::optional<Address> to;
    if (msg.kind == EVMC_CALL) {
        to = msg.recipient;
    }
    else if (msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE) {
        to = msg.code_address;
    }

    frames_.emplace_back(CallFrame{
        .type =
            [kind = msg.kind] {
                switch (kind) {
                case EVMC_CALL:
                    return CallType::CALL;
                case EVMC_DELEGATECALL:
                    return CallType::DELEGATECALL;
                case EVMC_CALLCODE:
                    return CallType::CALLCODE;
                case EVMC_CREATE:
                    return CallType::CREATE;
                case EVMC_CREATE2:
                    return CallType::CREATE2;
                case EVMC_EOFCREATE:
                    MONAD_ABORT(); // unsupported
                }
                MONAD_ABORT(); // unreachable
            }(),
        .flags = msg.flags,
        .from = from,
        .to = to,
        .value = load_be<uint256_t>(msg.value),
        .gas = depth == 0 ? tx_.gas_limit : static_cast<uint64_t>(msg.gas),
        .gas_used = 0,
        .input = msg.input_data == nullptr
                     ? byte_string{}
                     : byte_string{msg.input_data, msg.input_size},
        .output = {},
        .status = EVMC_FAILURE,
        .depth = depth,
        .logs = std::vector<CallFrame::Log>{},
    });

    last_.push(frames_.size() - 1);
}

void CallTraceRunner::operator()(monad::trace::call_trace::Exit const &op)
{
    auto const &res = op.result;

    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(!last_.empty());
    MONAD_ASSERT(!positions_.empty());

    auto &frame = frames_.at(last_.top());

    MONAD_ASSERT(frame.gas >= static_cast<uint64_t>(res.gas_left));
    frame.gas_used = frame.gas - static_cast<uint64_t>(res.gas_left);

    if (res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT) {
        frame.output = res.output_size == 0
                           ? byte_string{}
                           : byte_string{res.output_data, res.output_size};
    }
    frame.status = res.status_code;

    if (frame.type == CallType::CREATE || frame.type == CallType::CREATE2) {
        frame.to = is_zero(res.create_address)
                       ? std::nullopt
                       : std::optional{res.create_address};
    }

    last_.pop();
    positions_.pop();
}

void CallTraceRunner::operator()(monad::trace::call_trace::Log const &op)
{
    Receipt::Log log = op.log;

    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(!last_.empty());
    MONAD_ASSERT(!positions_.empty());

    auto &frame = frames_.at(last_.top());
    MONAD_ASSERT(frame.logs.has_value());

    frame.logs->emplace_back(std::move(log), positions_.top());
}

void CallTraceRunner::operator()(
    monad::trace::call_trace::SelfDestruct const &op)
{
    auto const &from = op.from;
    auto const &to = op.to;
    auto const &transferred_balance = op.transferred_balance;

    MONAD_ASSERT(!last_.empty());
    MONAD_ASSERT(!positions_.empty());
    positions_.top()++;

    auto const &parent = frames_.at(last_.top());

    frames_.emplace_back(CallFrame{
        .type = CallType::SELFDESTRUCT,
        .flags = 0,
        .from = from,
        .to = to,
        .value = transferred_balance,
        .gas = 0,
        .gas_used = 0,
        .input = {},
        .output = {},
        .status = EVMC_SUCCESS, // TODO
        .depth = parent.depth + 1,
        .logs = std::vector<CallFrame::Log>{},
    });
}

void CallTraceRunner::operator()(monad::trace::call_trace::Finish const &op)
{
    auto const gas_used = op.gas_used;

    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(last_.empty());
    frames_.front().gas_used = gas_used;
}

void CallTraceRunner::operator()(monad::trace::call_trace::Reset const &)
{
    frames_.clear();
    last_ = std::stack<size_t>{};

    positions_ = std::stack<size_t>{};
    positions_.push(0);
}

void CallTraceRunner::operator()(
    monad::trace::call_trace::GetCallFrames const &op)
{
    *op.call_frames = frames_;
}

void CallTraceRunner::operator()(
    monad::trace::call_trace::NativeTransfer const &op)
{
    // Skip emitting native transfer events when no value is transferred or
    // `from` and `to` are the same account (i.e. no net transfer of funds).
    if (log_native_transfers_ && op.transferred_balance > 0 &&
        op.from != op.to) {
        static constexpr Address native_token_address =
            0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_address;
        static constexpr bytes32_t signature =
            abi_encode_event_signature("Transfer(address,address,uint256)");
        static_assert(
            signature ==
            bytes32_from_hex("ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a"
                             "11628f55a4df523b3ef"));

        auto event =
            EventBuilder(native_token_address, signature)
                .add_topic(abi_encode_address(op.from))
                .add_topic(abi_encode_address(op.to))
                .add_data(abi_encode_uint(u256_be{op.transferred_balance}))
                .build();

        op.state.store_log(event);
        trace::call_trace::Log log_op{std::move(event)};
        (*this)(log_op);
    }
}

MONAD_NAMESPACE_END
