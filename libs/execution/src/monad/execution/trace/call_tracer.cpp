#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/fmt/address_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/trace/call_frame.hpp>
#include <monad/execution/trace/call_tracer.hpp>

#include <evmc/evmc.hpp>
#include <intx/intx.hpp>
#include <nlohmann/json.hpp>

#include <fstream>
#include <iomanip>
#include <optional>
#include <span>
#include <sstream>
#include <string>
#include <string_view>

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

void NoopCallTracer::on_self_destruct(
    Address const &, Address const &, uint256_t const &)
{
}

void NoopCallTracer::on_finish(uint64_t const) {}

std::vector<CallFrame> &&NoopCallTracer::get_frames() &&
{
    return std::move(frames_);
}

CallTracer::CallTracer(Transaction const &tx)
    : frames_{}
    , depth_{0}
    , tx_(tx)
{
    frames_.reserve(128);
}

void CallTracer::on_enter(evmc_message const &msg)
{
    depth_ = static_cast<uint64_t>(msg.depth);

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
                default:
                    MONAD_ASSERT(false);
                }
            }(),
        .flags = msg.flags,
        .from = from,
        .to = to,
        .value = intx::be::load<uint256_t>(msg.value),
        .gas = depth_ == 0 ? tx_.gas_limit : static_cast<uint64_t>(msg.gas),
        .gas_used = 0,
        .input = msg.input_data == nullptr
                     ? byte_string{}
                     : byte_string{msg.input_data, msg.input_size},
        .output = {},
        .status = EVMC_FAILURE,
        .depth = depth_,
    });

    last_.push(frames_.size() - 1);
}

void CallTracer::on_exit(evmc::Result const &res)
{
    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(!last_.empty());

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
        frame.to = res.create_address;
    }

    last_.pop();
}

void CallTracer::on_self_destruct(
    Address const &from, Address const &to, uint256_t const &refund)
{
    // we don't change depth_ here, because exit and enter combined
    // together here
    frames_.emplace_back(CallFrame{
        .type = CallType::SELFDESTRUCT,
        .flags = 0,
        .from = from,
        .to = to,
        .value = refund,
        .gas = 0,
        .gas_used = 0,
        .input = {},
        .output = {},
        .status = EVMC_SUCCESS, // The return status code is always SUCCESS for
                                // self-destruct
        .depth = depth_ + 1,
    });
}

void CallTracer::on_finish(uint64_t const gas_used)
{
    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(last_.empty());
    frames_.front().gas_used = gas_used;
}

std::vector<CallFrame> &&CallTracer::get_frames() &&
{
    return std::move(frames_);
}

nlohmann::json CallTracer::to_json() const
{
    MONAD_ASSERT(!frames_.empty());
    MONAD_ASSERT(frames_[0].depth == 0);

    size_t pos = 0;

    nlohmann::json res{};
    auto const hash = keccak256(rlp::encode_transaction(tx_));
    auto const key = fmt::format(
        "0x{:02x}", fmt::join(std::as_bytes(std::span(hash.bytes)), ""));
    nlohmann::json value{};
    to_json_helper(frames_, value, pos);
    res[key] = value;

    return res;
}

MONAD_NAMESPACE_END
