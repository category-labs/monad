#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>

#include <evmc/evmc.hpp>
#include <nlohmann/json_fwd.hpp>

#include <optional>
#include <span>
#include <stack>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct CallFrame;
struct Receipt;
struct Transaction;

struct CallTracerBase
{
    virtual void on_enter(evmc_message const &) = 0;
    virtual void on_exit(evmc::Result const &) = 0;
    virtual void on_self_destruct(Address const &from, Address const &to) = 0;
    virtual void on_receipt(Receipt const &) = 0;
    virtual std::span<CallFrame const> get_frames() const = 0;
};

struct NoopCallTracer final : public CallTracerBase
{
    virtual void on_enter(evmc_message const &) override;
    virtual void on_exit(evmc::Result const &) override;
    virtual void on_self_destruct(Address const &, Address const &) override;
    virtual void on_receipt(Receipt const &) override;
    virtual std::span<CallFrame const> get_frames() const override;
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
    virtual void on_receipt(Receipt const &) override;
    virtual std::span<CallFrame const> get_frames() const override;

    nlohmann::json to_json() const;
};

MONAD_NAMESPACE_END
