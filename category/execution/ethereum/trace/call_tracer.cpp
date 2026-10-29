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
#include <category/core/basic_formatter.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/status_code.h>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/ranges.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>
#include <span>
#include <stack>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    void to_json_helper(
        std::span<CallFrame const> const frames, nlohmann::json &json,
        size_t &pos)
    {
        if (pos >= frames.size()) {
            return;
        }
        json = to_json(frames[pos]);

        while (pos + 1 < frames.size()) {
            MONAD_ASSERT_THROW(
                json.contains("depth"),
                "JSON object does not contain 'depth' key");
            if (frames[pos + 1].depth > json["depth"]) {
                nlohmann::json j;
                pos++;
                to_json_helper(frames, j, pos);
                json["calls"].push_back(j);
            }
            else {
                return;
            }
        }
    }
}

void NoopCallTracer::on_enter(evmc_message const &) {}

void NoopCallTracer::on_exit(evmc::Result const &) {}

void NoopCallTracer::on_log(Receipt::Log) {}

void NoopCallTracer::on_self_destruct(
    Address const &, Address const &, uint256_t const &)
{
}

void NoopCallTracer::on_finish(uint64_t const) {}

void NoopCallTracer::reset() {}

std::span<CallFrame const> NoopCallTracer::get_call_frames() const
{
    return {};
}

CallTracer::CallTracer(Transaction const &tx, std::vector<CallFrame> &frames)
    : CallTracer(tx, frames, std::numeric_limits<size_t>::max())
{
}

CallTracer::CallFramesStack::CallFramesStack(std::vector<CallFrame> &frames)
    : frames_(frames)
{
    positions_.push(0);
}

void CallTracer::CallFramesStack::advance_position()
{
    MONAD_ASSERT_THROW(!positions_.empty(), "Positions stack is empty");
    positions_.top()++;
}

CallFrame &CallTracer::CallFramesStack::top_frame()
{
    MONAD_ASSERT_THROW(!last_.empty(), "Last stack is empty");
    return frames_.at(last_.top());
}

CallFrame &CallTracer::CallFramesStack::pop_frame()
{
    MONAD_ASSERT_THROW(!frames_.empty(), "Frames vector is empty");
    MONAD_ASSERT_THROW(!last_.empty(), "Last stack is empty");
    MONAD_ASSERT_THROW(!positions_.empty(), "Positions stack is empty");

    auto &frame = frames_.at(last_.top());
    last_.pop();
    positions_.pop();
    return frame;
}

CallFrame &CallTracer::CallFramesStack::push_frame(CallFrame &&frame)
{
    advance_position();
    positions_.push(0);
    frames_.emplace_back(std::move(frame));
    last_.push(frames_.size() - 1);
    return frames_.back();
}

CallFrame &
CallTracer::CallFramesStack::push_selfdestruct_frame(CallFrame &&frame)
{
    // A selfdestruct requires an active frame on the stack.
    MONAD_ASSERT_THROW(!last_.empty(), "Last stack is empty");
    advance_position();
    frames_.emplace_back(std::move(frame));
    return frames_.back();
}

bool CallTracer::CallFramesStack::has_active_frame() const
{
    return !last_.empty();
}

size_t CallTracer::CallFramesStack::position() const
{
    MONAD_ASSERT_THROW(!positions_.empty(), "Positions stack is empty");
    return positions_.top();
}

void CallTracer::CallFramesStack::reset()
{
    last_ = std::stack<size_t>{};
    positions_ = std::stack<size_t>{};
    positions_.push(0);
}

CallTracer::BoundedSize::BoundedSize(size_t const max)
    : max_(max)
{
}

CallTracer::BoundedSize::operator bool() const noexcept
{
    return !exceeded_;
}

CallTracer::BoundedSize &
CallTracer::BoundedSize::operator+=(size_t const additional_size) noexcept
{
    if (exceeded_) {
        return *this;
    }

    if (additional_size > max_ - current_) {
        exceeded_ = true;
    }
    else {
        current_ += additional_size;
    }

    return *this;
}

void CallTracer::BoundedSize::reset() noexcept
{
    current_ = 0;
    exceeded_ = false;
}

CallTracer::CallTracer(
    Transaction const &tx, std::vector<CallFrame> &frames,
    size_t const max_size)
    : frames_(frames)
    , frames_stack_(frames_)
    , tx_(tx)
    , size_(max_size)
{
    size_t const initial_capacity =
        std::min<size_t>(128, max_size / sizeof(CallFrame));
    frames_.reserve(initial_capacity);
}

void CallTracer::on_enter(evmc_message const &msg)
{
    if (!(size_ += sizeof(CallFrame)) || !(size_ += msg.input_size)) {
        return;
    }

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

    frames_stack_.push_frame(CallFrame{
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
        .status = MONAD_STATUS_FAILURE,
        .depth = depth,
        .logs = std::vector<CallFrame::Log>{},
    });
}

void CallTracer::on_exit(evmc::Result const &res)
{
    size_t const output_size =
        res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT
            ? res.output_size
            : 0;
    if (!(size_ += output_size)) {
        return;
    }

    CallFrame &frame = frames_stack_.pop_frame();

    MONAD_ASSERT_THROW(
        frame.gas >= static_cast<uint64_t>(res.gas_left),
        "Frame gas is less than remaining gas");
    frame.gas_used = frame.gas - static_cast<uint64_t>(res.gas_left);

    if (res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT) {
        frame.output = res.output_size == 0
                           ? byte_string{}
                           : byte_string{res.output_data, res.output_size};
    }
    frame.status = from_evmc_status_code(res.status_code);

    if (frame.type == CallType::CREATE || frame.type == CallType::CREATE2) {
        frame.to = is_zero(res.create_address)
                       ? std::nullopt
                       : std::optional{res.create_address};
    }
}

void CallTracer::on_log(Receipt::Log log)
{
    if (!(size_ += sizeof(CallFrame::Log)) || !(size_ += log.data.size())) {
        return;
    }
    for (auto const &topic : log.topics) {
        if (!(size_ += sizeof(topic))) {
            return;
        }
    }

    auto &frame = frames_stack_.top_frame();
    MONAD_ASSERT_THROW(
        frame.logs.has_value(), "Frame logs are not initialized");

    frame.logs->emplace_back(std::move(log), frames_stack_.position());
}

void CallTracer::on_self_destruct(
    Address const &from, Address const &to,
    uint256_t const &transferred_balance)
{
    if (!(size_ += sizeof(CallFrame))) {
        return;
    }

    auto &parent = frames_stack_.top_frame();

    frames_stack_.push_selfdestruct_frame(CallFrame{
        .type = CallType::SELFDESTRUCT,
        .flags = 0,
        .from = from,
        .to = to,
        .value = transferred_balance,
        .gas = 0,
        .gas_used = 0,
        .input = {},
        .output = {},
        .status = MONAD_STATUS_SUCCESS, // TODO
        .depth = parent.depth + 1,
        .logs = std::vector<CallFrame::Log>{},
    });
}

void CallTracer::on_finish(uint64_t const gas_used)
{
    if (!size_) {
        return;
    }

    MONAD_ASSERT_THROW(!frames_.empty(), "Frames vector is empty");
    MONAD_ASSERT_THROW(
        !frames_stack_.has_active_frame(),
        "There is an active frame on the stack");
    frames_.front().gas_used = gas_used;
}

void CallTracer::reset()
{
    frames_.clear();
    frames_stack_.reset();
    size_.reset();
}

std::span<CallFrame const> CallTracer::get_call_frames() const
{
    return frames_;
}

void CallTracer::check_size_limit() const
{
    MONAD_ASSERT_THROW(
        static_cast<bool>(size_),
        "call trace size exceeds maximum allowed size");
}

nlohmann::json CallTracer::to_json() const
{
    check_size_limit();
    nlohmann::json res{};
    auto const hash = keccak256(rlp::encode_transaction(tx_));
    auto const key = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(hash.bytes)), ""));
    nlohmann::json value{};

    MONAD_ASSERT_THROW(!frames_.empty(), "Frames vector is empty");
    MONAD_ASSERT_THROW(frames_[0].depth == 0, "First frame depth is not zero");
    size_t pos = 0;
    to_json_helper(frames_, value, pos);

    res[key] = value;

    return res;
}

MONAD_NAMESPACE_END
