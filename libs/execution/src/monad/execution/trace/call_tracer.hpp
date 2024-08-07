#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <ethash/hash_types.hpp>

#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>

#include <quill/Quill.h> // NOLINT

#include <filesystem>
#include <map>
#include <optional>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    inline constexpr uint64_t g_star(
        evmc_revision const &rev, uint64_t const gas_limit,
        uint64_t const gas_remaining, uint64_t const refund,
        bool const top_level = false)
    {
        // EIP-3529
        if (top_level) {
            auto const max_refund_quotient = rev >= EVMC_LONDON ? 5u : 2u;
            auto const refund_allowance =
                (gas_limit - gas_remaining) / max_refund_quotient;

            return gas_remaining + std::min(refund_allowance, refund);
        }
        else {
            return gas_remaining;
        }
    }
}

enum class CallKind
{
    CALL = 0,
    DELEGATECALL,
    CALLCODE,
    CREATE,
    CREATE2,
    SELFDESTRUCT,
};

struct CallFrame
{
    CallKind type;
    uint64_t flags{0};
    Address from;
    std::optional<Address> to{std::nullopt};
    uint256_t value; // amount of value transfer
    uint64_t gas;
    uint64_t gas_used{0};
    byte_string input{};
    byte_string output{};
    evmc_status_code status{EVMC_SUCCESS};

    uint64_t depth;

    // for debug only
    nlohmann::json to_json() const; // key = hash(tx)

    friend bool operator==(CallFrame const &, CallFrame const &) = default;

    // TODO: official documentation doesn't contain "logs", but geth/reth
    // implementation does
};

using TxnCallFrames = std::vector<CallFrame>;
using BlockCallFrames = std::vector<TxnCallFrames>;

class CallTracer
{
    TxnCallFrames call_frames_{};
    std::unordered_map<size_t, size_t> depth_to_last_pos_{};
    size_t depth_;

    Transaction const &tx_;

    // debug helper
    hash256 tx_hash_;

public:
    CallTracer() = delete;
    CallTracer(CallTracer const &) = delete;
    CallTracer(CallTracer &&) = delete;

    explicit CallTracer(Transaction const &);

    // called when entering a new frame
    template <evmc_revision rev>
    void on_enter(evmc_message const &msg)
    {
        depth_ = static_cast<size_t>(msg.depth);

        Address from = msg.sender;
        // This is to conform with quicknode RPC
        if (msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE) {
            from = msg.recipient;
        }

        std::optional<Address> to = std::nullopt;
        if (msg.kind == EVMC_CALL) {
            to = std::make_optional(msg.recipient);
        }
        else if (msg.kind == EVMC_DELEGATECALL || msg.kind == EVMC_CALLCODE) {
            to = std::make_optional(msg.code_address);
        }

        CallFrame call_frame{
            .type = static_cast<CallKind>(msg.kind),
            .flags = static_cast<uint64_t>(msg.flags),
            .from = from,
            .to = to,
            .value = intx::be::load<uint256_t>(msg.value),
            .gas = call_frames_.empty() ? static_cast<uint64_t>(msg.gas) +
                                              intrinsic_gas<rev>(tx_)
                                        : static_cast<uint64_t>(msg.gas),
            .input = msg.input_data == nullptr
                         ? byte_string{}
                         : byte_string{msg.input_data, msg.input_size},
            .depth = static_cast<uint64_t>(msg.depth),
        };

        call_frames_.emplace_back(std::move(call_frame));
        depth_to_last_pos_[depth_] = call_frames_.size() - 1;
    }

    // called when exiting the current frame
    template <evmc_revision rev>
    void on_exit(evmc::Result const &res)
    {
        MONAD_ASSERT(!call_frames_.empty());

        auto it = depth_to_last_pos_.find(depth_);
        MONAD_ASSERT(it != depth_to_last_pos_.end());
        auto &frame = call_frames_[it->second];

        auto const gas_limit = frame.gas;
        auto const gas_remaining = g_star(
            rev,
            gas_limit,
            static_cast<uint64_t>(res.gas_left),
            static_cast<uint64_t>(res.gas_refund),
            depth_ == 0);
        frame.gas_used = gas_limit - gas_remaining;

        if (res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT) {
            frame.output = res.output_size == 0
                               ? byte_string{}
                               : byte_string{res.output_data, res.output_size};
        }
        frame.status = res.status_code;

        if (frame.type == CallKind::CREATE || frame.type == CallKind::CREATE2) {
            frame.to = res.create_address;
        }

        depth_to_last_pos_.erase(it);
        if (depth_) {
            depth_--;
        }
    }

    void on_self_destruct(Address const &from, Address const &to)
    {
        CallFrame call_frame{
            .type = CallKind::SELFDESTRUCT,
            .from = from,
            .to = to,
            .value = 0,
            .gas = 0,
            .gas_used = 0,
            .status = EVMC_SUCCESS, // TODO
            .depth = depth_ + 1,
        };

        // we don't change depth_ here, because exit and enter combined together
        // here
        call_frames_.emplace_back(std::move(call_frame));
    }

    TxnCallFrames get_call_frames() const
    {
        return call_frames_;
    }

    //////////////////////// debug helpers ////////////////////////
    hash256 get_tx_hash() const
    {
        return tx_hash_;
    }

    nlohmann::json to_json();

private:
    //////////////////////// debug helpers ////////////////////////
    void to_json_helper(nlohmann::json &, size_t &pos);
};

MONAD_NAMESPACE_END
