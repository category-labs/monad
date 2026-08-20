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
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <quill/bundled/fmt/ranges.h>

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
    nlohmann::json make_truncated_call_frame(uint64_t const depth)
    {
        nlohmann::json frame;
        frame["type"] = "TRUNCATED";
        frame["from"] = "0x0000000000000000000000000000000000000000";
        frame["to"] = "0x0000000000000000000000000000000000000000";
        frame["value"] = "0x0";
        frame["gas"] = "0x0";
        frame["gasUsed"] = "0x0";
        frame["input"] = "0x";
        frame["output"] = "0x";
        frame["error"] = "trace truncated";
        frame["depth"] = depth;
        frame["calls"] = nlohmann::json::array();
        return frame;
    }

    void to_json_helper(
        std::span<CallFrame const> const frames, nlohmann::json &json,
        size_t &pos)
    {
        if (pos >= frames.size()) {
            return;
        }
        json = to_json(frames[pos]);

        while (pos + 1 < frames.size()) {
            MONAD_ASSERT(json.contains("depth"));
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

bool NoopCallTracer::truncated() const
{
    return false;
}

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

void CallTracer::CallFramesStack::record_dropped_subtree_enter()
{
    if (!last_.empty()) {
        advance_position();
    }
    dropped_subtree_depth_ = 1;
}

void CallTracer::CallFramesStack::record_dropped_subtree_child_enter()
{
    MONAD_ASSERT(dropped_subtree_depth_ > 0);
    dropped_subtree_depth_++;
}

void CallTracer::CallFramesStack::advance_position()
{
    MONAD_ASSERT(!positions_.empty());
    positions_.top()++;
}

bool CallTracer::CallFramesStack::consume_dropped_exit()
{
    if (dropped_subtree_depth_ == 0) {
        return false;
    }

    dropped_subtree_depth_--;
    return true;
}

CallFrame &CallTracer::CallFramesStack::top_frame()
{
    MONAD_ASSERT(!last_.empty());
    return frames_.at(last_.top());
}

CallFrame &CallTracer::CallFramesStack::pop_frame()
{
    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(!last_.empty());
    MONAD_ASSERT(!positions_.empty());

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
    MONAD_ASSERT(!last_.empty());
    advance_position();
    frames_.emplace_back(std::move(frame));
    return frames_.back();
}

bool CallTracer::CallFramesStack::has_active_frame() const
{
    return !last_.empty();
}

bool CallTracer::CallFramesStack::in_dropped_subtree() const
{
    return dropped_subtree_depth_ > 0;
}

size_t CallTracer::CallFramesStack::dropped_subtree_depth() const
{
    return dropped_subtree_depth_;
}

size_t CallTracer::CallFramesStack::position() const
{
    MONAD_ASSERT(!positions_.empty());
    return positions_.top();
}

void CallTracer::CallFramesStack::reset()
{
    last_ = std::stack<size_t>{};
    positions_ = std::stack<size_t>{};
    positions_.push(0);
    dropped_subtree_depth_ = 0;
}

CallTracer::CallTracer(
    Transaction const &tx, std::vector<CallFrame> &frames,
    size_t const max_size)
    : frames_(frames)
    , frames_stack_(frames_)
    , tx_(tx)
    , max_size_(max_size)
    , size_(0)
{
    frames_.reserve(128);
}

bool CallTracer::fits(size_t const additional_size) const
{
    if (size_ >= max_size_) {
        return false;
    }

    return additional_size <= (max_size_ - size_);
}

size_t CallTracer::log_size(Receipt::Log const &log) const
{
    size_t entry_size = sizeof(CallFrame::Log) + log.data.size();
    for (auto const &topic : log.topics) {
        entry_size += sizeof(topic);
    }
    return entry_size;
}

void CallTracer::on_enter(evmc_message const &msg)
{
    if (frames_stack_.in_dropped_subtree()) {
        frames_stack_.record_dropped_subtree_child_enter();
        return;
    }

    if (truncated_) {
        frames_stack_.record_dropped_subtree_enter();
        return;
    }

    auto const frame_size = sizeof(CallFrame) + msg.input_size;

    if (!fits(frame_size)) {
        truncated_ = true;
        frames_stack_.record_dropped_subtree_enter();
        return;
    }

    byte_string const input = msg.input_data == nullptr
                                  ? byte_string{}
                                  : byte_string{msg.input_data, msg.input_size};

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
        .status = EVMC_FAILURE,
        .depth = depth,
        .logs = std::vector<CallFrame::Log>{},
    });

    size_ += frame_size;
}

void CallTracer::on_exit(evmc::Result const &res)
{
    if (frames_stack_.consume_dropped_exit()) {
        return;
    }

    CallFrame &frame = frames_stack_.pop_frame();

    MONAD_ASSERT(frame.gas >= static_cast<uint64_t>(res.gas_left));
    frame.gas_used = frame.gas - static_cast<uint64_t>(res.gas_left);

    if (res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT) {
        if (res.output_size == 0) {
            frame.output = byte_string{};
        }
        else if (fits(res.output_size)) {
            frame.output = byte_string{res.output_data, res.output_size};
            size_ += res.output_size;
        }
        else {
            frame.output = byte_string{};
            truncated_ = true;
        }
    }
    frame.status = res.status_code;

    if (frame.type == CallType::CREATE || frame.type == CallType::CREATE2) {
        frame.to = is_zero(res.create_address)
                       ? std::nullopt
                       : std::optional{res.create_address};
    }
}

void CallTracer::on_log(Receipt::Log log)
{
    if (frames_stack_.in_dropped_subtree()) {
        truncated_ = true;
        return;
    }

    auto const entry_size = log_size(log);
    if (!fits(entry_size)) {
        truncated_ = true;
        return;
    }

    auto &frame = frames_stack_.top_frame();
    MONAD_ASSERT(frame.logs.has_value());

    frame.logs->emplace_back(std::move(log), frames_stack_.position());
    size_ += entry_size;
}

void CallTracer::on_self_destruct(
    Address const &from, Address const &to,
    uint256_t const &transferred_balance)
{
    if (frames_stack_.in_dropped_subtree()) {
        truncated_ = true;
        return;
    }

    if (!fits(sizeof(CallFrame))) {
        truncated_ = true;
        frames_stack_.advance_position();
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
        .status = EVMC_SUCCESS, // TODO
        .depth = parent.depth + 1,
        .logs = std::vector<CallFrame::Log>{},
    });

    size_ += sizeof(CallFrame);
}

void CallTracer::on_finish(uint64_t const gas_used)
{
    MONAD_ASSERT(frames_stack_.dropped_subtree_depth() == 0);
    MONAD_ASSERT(!frames_stack_.has_active_frame());

    if (frames_.empty()) {
        return;
    }

    frames_.front().gas_used = gas_used;
}

void CallTracer::reset()
{
    frames_.clear();
    frames_stack_.reset();
    size_ = 0;
    truncated_ = false;
}

std::span<CallFrame const> CallTracer::get_call_frames() const
{
    return frames_;
}

bool CallTracer::truncated() const
{
    return truncated_;
}

nlohmann::json CallTracer::to_json() const
{
    nlohmann::json res{};
    auto const hash = keccak256(rlp::encode_transaction(tx_));
    auto const key = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(hash.bytes)), ""));
    nlohmann::json value{};

    if (!frames_.empty()) {
        MONAD_ASSERT(frames_[0].depth == 0);
        size_t pos = 0;
        to_json_helper(frames_, value, pos);
        if (truncated_) {
            value["calls"].push_back(
                make_truncated_call_frame(frames_[0].depth + 1));
        }
    }
    else {
        MONAD_ASSERT(truncated_);
        value = make_truncated_call_frame(0);
    }

    res[key] = value;

    return res;
}

MONAD_NAMESPACE_END
