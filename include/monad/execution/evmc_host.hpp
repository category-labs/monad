#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/execution/transaction_gas.hpp>
#include <monad/state2/state.hpp>

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

protected:
    State &state_;

public:
    EvmcHostBase(EvmcHostBase const &, State &) noexcept;

    EvmcHostBase(
        evmc_tx_context const &, BlockHashBuffer const &, State &) noexcept;

    virtual ~EvmcHostBase() noexcept = default;

    virtual bytes32_t get_storage(
        address_t const &, bytes32_t const &key) const noexcept override;

    virtual evmc_storage_status set_storage(
        address_t const &, bytes32_t const &key,
        bytes32_t const &value) noexcept override;

    virtual evmc::uint256be
    get_balance(address_t const &) const noexcept override;

    virtual size_t get_code_size(address_t const &) const noexcept override;

    virtual bytes32_t get_code_hash(address_t const &) const noexcept override;

    virtual size_t copy_code(
        address_t const &, size_t offset, uint8_t *data,
        size_t size) const noexcept override;

    [[nodiscard]] virtual bool selfdestruct(
        address_t const &address,
        address_t const &beneficiary) noexcept override;

    virtual evmc_tx_context get_tx_context() const noexcept override;

    virtual bytes32_t get_block_hash(int64_t) const noexcept override;

    virtual void emit_log(
        address_t const &, uint8_t const *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) noexcept override;

    virtual evmc_access_status
    access_storage(address_t const &, bytes32_t const &key) noexcept override;
};

template <evmc_revision rev>
struct EvmcHost final : public EvmcHostBase
{
    using EvmcHostBase::EvmcHostBase;

    virtual bool
    account_exists(address_t const &address) const noexcept override
    {
        if constexpr (rev < EVMC_SPURIOUS_DRAGON) {
            return state_.account_exists(address);
        }
        return !state_.account_is_dead(address);
    }

    [[nodiscard]] virtual evmc::Result
    call(evmc_message const &msg) noexcept override
    {
        if (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2) {
            auto res = create_contract_account<rev>(this, state_, msg);
            // eip-211, eip-140
            if (res.status_code != EVMC_REVERT) {
                return evmc::Result{
                    res.status_code,
                    res.gas_left,
                    res.gas_refund,
                    res.create_address};
            }
            return res;
        }

        return call_evm<rev>(this, state_, msg);
    }

    virtual evmc_access_status
    access_account(address_t const &address) noexcept override
    {
        if (is_precompile<rev>(address)) {
            return EVMC_ACCESS_WARM;
        }
        return state_.access_account(address);
    }
};

MONAD_NAMESPACE_END
