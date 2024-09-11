#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <ethash/hash_types.hpp>

#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>

#include <quill/Quill.h> // NOLINT

#include <filesystem>
#include <optional>
#include <stack>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

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
    uint32_t flags{0};
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

struct CallTracerBase
{
    virtual void on_enter(evmc_message const &) = 0;
    virtual void on_exit(evmc::Result const &) = 0;
    virtual void on_self_destruct(Address const &from, Address const &to) = 0;
    virtual void on_receipt(Receipt const &) = 0;
    virtual TxnCallFrames get_frames() const = 0;
};

struct NoopCallTracer final : public CallTracerBase
{
    virtual void on_enter(evmc_message const &) override {}

    virtual void on_exit(evmc::Result const &) override {}

    virtual void on_self_destruct(Address const &, Address const &) override {}

    virtual void on_receipt(Receipt const &) override {};

    virtual TxnCallFrames get_frames() const override
    {
        return {};
    };
};

class CallTracer final : public CallTracerBase
{
    TxnCallFrames frames_{};
    std::stack<size_t> last_;
    uint64_t depth_;
    Transaction const &tx_;

public:
    CallTracer() = delete;
    CallTracer(CallTracer const &) = delete;
    CallTracer(CallTracer &&) = delete;

    explicit CallTracer(Transaction const &);

    virtual void on_enter(evmc_message const &msg) override
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
            .type = static_cast<CallKind>(msg.kind),
            .flags = msg.flags,
            .from = from,
            .to = to,
            .value = intx::be::load<uint256_t>(msg.value),
            .gas = depth_ == 0 ? tx_.gas_limit : static_cast<uint64_t>(msg.gas),
            .gas_used = 0,
            .input = msg.input_data == nullptr
                         ? byte_string{}
                         : byte_string{msg.input_data, msg.input_size},
            .output{},
            .status{EVMC_FAILURE},
            .depth = depth_,
        });

        last_.push(frames_.size() - 1);
    }

    virtual void on_exit(evmc::Result const &res) override
    {
        MONAD_ASSERT(!frames_.empty());
        MONAD_ASSERT(!last_.empty());

        auto &frame = frames_.at(last_.top());

        frame.gas_used = frame.gas - res.gas_left;

        if (res.status_code == EVMC_SUCCESS || res.status_code == EVMC_REVERT) {
            frame.output = res.output_size == 0
                               ? byte_string{}
                               : byte_string{res.output_data, res.output_size};
        }
        frame.status = res.status_code;

        if (frame.type == CallKind::CREATE || frame.type == CallKind::CREATE2) {
            frame.to = res.create_address;
        }

        last_.pop();
    }

    virtual void
    on_self_destruct(Address const &from, Address const &to) override
    {
        // we don't change depth_ here, because exit and enter combined
        // together here
        frames_.emplace_back(CallFrame{
            .type = CallKind::SELFDESTRUCT,
            .flags = 0,
            .from = from,
            .to = to,
            .value = 0,
            .gas = 0,
            .gas_used = 0,
            .input = {},
            .output = {},
            .status = EVMC_SUCCESS, // TODO
            .depth = depth_ + 1,
        });
    }

    virtual void on_receipt(Receipt const &receipt)
    {
        MONAD_ASSERT(!frames_.empty());
        MONAD_ASSERT(last_.empty());
        frames_.front().gas_used = receipt.gas_used;
    }

    virtual TxnCallFrames get_frames() const override
    {
        return frames_;
    }

    //////////////////////// debug helpers ////////////////////////
    nlohmann::json to_json();
};

MONAD_NAMESPACE_END
