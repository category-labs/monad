#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/state3/state.hpp>

#include <intx/intx.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <utility>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;

class EvmcHostBase : public evmc::Host
{
    evmc_tx_context const &tx_context_;
    BlockHashBuffer const &block_hash_buffer_;
    friend class TimeReset;

protected:
    State &state_;
    CallTracerBase &call_tracer_;
    size_t const max_code_size_;
    std::chrono::time_point<std::chrono::system_clock> start_time_;
    std::atomic<uint64_t> exec_time_{};

public:
    EvmcHostBase(
        CallTracerBase &, evmc_tx_context const &, BlockHashBuffer const &,
        State &, size_t max_code_size) noexcept;

    virtual ~EvmcHostBase() noexcept = default;

    virtual bytes32_t
    get_storage(Address const &, bytes32_t const &key) const noexcept override;

    virtual evmc_storage_status set_storage(
        Address const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;

    virtual evmc::uint256be
    get_balance(Address const &) const noexcept override;

    virtual size_t get_code_size(Address const &) const noexcept override;

    virtual bytes32_t get_code_hash(Address const &) const noexcept override;

    virtual size_t copy_code(
        Address const &, size_t offset, uint8_t *data,
        size_t size) const noexcept override;

    virtual evmc_tx_context get_tx_context() const noexcept override;

    virtual bytes32_t get_block_hash(int64_t) const noexcept override;

    virtual void emit_log(
        Address const &, uint8_t const *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) noexcept override;

    virtual evmc_access_status
    access_storage(Address const &, bytes32_t const &key) noexcept override;

    virtual bytes32_t get_transient_storage(
        Address const &, bytes32_t const &key) const noexcept override;

    virtual void set_transient_storage(
        Address const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;
};


class TimeReset
    {
    public:
        TimeReset(EvmcHostBase *ctx)
            : ctx_{*ctx}
        {
#ifdef ENABLE_EVM_TIMING
            auto t = std::chrono::system_clock::now();
            auto d = std::chrono::duration_cast<std::chrono::nanoseconds>(
                t - ctx->start_time_);

            ctx_.exec_time_.fetch_add(d.count());
        }

        ~TimeReset()
        {
            ctx_.start_time_ = std::chrono::system_clock::now();
#endif
        }
    private:
    EvmcHostBase &ctx_;
    };

template <evmc_revision rev>
struct EvmcHost final : public EvmcHostBase
{
    using EvmcHostBase::EvmcHostBase;

    virtual bool account_exists(Address const &address) const noexcept override
    {
        TimeReset _{const_cast<EvmcHost<rev>*>(this)};
        if constexpr (rev < EVMC_SPURIOUS_DRAGON) {
            return state_.account_exists(address);
        }
        return !state_.account_is_dead(address);
    }

    virtual bool selfdestruct(
        Address const &address, Address const &beneficiary) noexcept override
    {
        TimeReset _{this};
        call_tracer_.on_self_destruct(address, beneficiary);
        return state_.selfdestruct<rev>(address, beneficiary);
    }

    virtual evmc::Result call(evmc_message const &msg) noexcept override
    {
#ifdef ENABLE_EVM_TIMING

        if(msg.depth > 0)
        {
            auto time = std::chrono::system_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(time - start_time_);
            exec_time_.fetch_add(duration.count());
        }
        start_time_ = std::chrono::system_clock::now();
#endif
        if (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2) {
            auto result =
                ::monad::create<rev>(this, state_, msg, max_code_size_);

            // EIP-211
            if (result.status_code != EVMC_REVERT) {
                result = evmc::Result{
                    result.status_code,
                    result.gas_left,
                    result.gas_refund,
                    result.create_address};
            }
#ifdef ENABLE_EVM_TIMING
            auto time = std::chrono::system_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(time - start_time_);
            exec_time_.fetch_add(duration.count());
#endif
            return result;
        }
        else {
            auto result = ::monad::call(this, state_, msg);
#ifdef ENABLE_EVM_TIMING
            auto time = std::chrono::system_clock::now();
            auto duration = std::chrono::duration_cast<std::chrono::nanoseconds>(time - start_time_);
            exec_time_.fetch_add(duration.count());
#endif
            return result;
        }
    }

    virtual evmc_access_status
    access_account(Address const &address) noexcept override
    {
        TimeReset _{this};
        if (is_precompile<rev>(address)) {
            return EVMC_ACCESS_WARM;
        }
        return state_.access_account(address);
    }

    CallTracerBase &get_call_tracer() noexcept
    {
        return call_tracer_;
    }

    std::atomic<uint64_t> &get_exec_time() noexcept
    {
        return exec_time_;
    }
};

MONAD_NAMESPACE_END
