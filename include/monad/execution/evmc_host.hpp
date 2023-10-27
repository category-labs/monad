#pragma once

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/execution/transaction_gas.hpp>

#include <intx/intx.hpp>

#include <evmc/evmc.hpp>

#include <utility>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, class TTraits>
struct EvmcHost : public evmc::Host
{
    using evm_t = Evm<TState, TTraits>;

    BlockHashBuffer const &block_hash_buffer_;
    BlockHeader const &header_;
    Transaction const &transaction_;
    TState &state_;

    using uint256be = evmc::uint256be;

    EvmcHost(EvmcHost const &host, TState &state)
        : block_hash_buffer_{host.block_hash_buffer_}
        , header_{host.header_}
        , transaction_{host.transaction_}
        , state_{state}
    {
    }

    EvmcHost(
        BlockHashBuffer const &block_hash_buffer, BlockHeader const &header,
        Transaction const &txn, TState &state) noexcept
        : block_hash_buffer_{block_hash_buffer}
        , header_{header}
        , transaction_{txn}
        , state_{state}
    {
    }
    virtual ~EvmcHost() noexcept = default;

    virtual bool
    account_exists(address_t const &address) const noexcept override
    {
        if constexpr (TTraits::rev < EVMC_SPURIOUS_DRAGON) {
            return state_.account_exists(address);
        }
        return !state_.account_is_dead(address);
    }

    virtual bytes32_t get_storage(
        address_t const &address, bytes32_t const &key) const noexcept override
    {
        return state_.get_storage(address, key);
    }

    virtual evmc_storage_status set_storage(
        address_t const &address, bytes32_t const &key,
        bytes32_t const &value) noexcept override
    {
        return state_.set_storage(address, key, value);
    }

    virtual uint256be
    get_balance(address_t const &address) const noexcept override
    {
        return state_.get_balance(address);
    }

    virtual size_t
    get_code_size(address_t const &address) const noexcept override
    {
        return state_.get_code_size(address);
    }

    virtual bytes32_t
    get_code_hash(address_t const &address) const noexcept override
    {
        if (state_.account_is_dead(address)) {
            return bytes32_t{};
        }
        return state_.get_code_hash(address);
    }

    virtual size_t copy_code(
        address_t const &address, size_t offset, uint8_t *data,
        size_t size) const noexcept override
    {
        return state_.copy_code(address, offset, data, size);
    }

    [[nodiscard]] virtual bool selfdestruct(
        address_t const &address,
        address_t const &beneficiary) noexcept override
    {
        return state_.selfdestruct(address, beneficiary);
    }

    [[nodiscard]] static constexpr evmc_message
    make_msg_from_txn(Transaction const &txn)
    {
        auto const to_address = [&] {
            if (txn.to) {
                return std::pair{EVMC_CALL, *txn.to};
            }
            return std::pair{EVMC_CREATE, address_t{}};
        }();

        evmc_message msg{
            .kind = to_address.first,
            .gas = static_cast<int64_t>(
                txn.gas_limit - intrinsic_gas<TTraits>(txn)),
            .recipient = to_address.second,
            .sender = *txn.from,
            .input_data = txn.data.data(),
            .input_size = txn.data.size(),
            .code_address = to_address.second,
        };
        intx::be::store(msg.value.bytes, txn.value);
        return msg;
    }

    [[nodiscard]] virtual evmc::Result
    call(evmc_message const &msg) noexcept override
    {
        if (msg.kind == EVMC_CREATE || msg.kind == EVMC_CREATE2) {
            auto res = evm_t::create_contract_account(this, state_, msg);
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

        return evm_t::call_evm(this, state_, msg);
    }

    virtual evmc_tx_context get_tx_context() const noexcept override
    {
        evmc_tx_context result{
            .tx_origin = *transaction_.from,
            .block_coinbase = header_.beneficiary,
            .block_number = static_cast<int64_t>(header_.number),
            .block_timestamp = static_cast<int64_t>(header_.timestamp),
            .block_gas_limit = static_cast<int64_t>(header_.gas_limit)};

        uint256_t const gas_cost = gas_price<TTraits>(
            transaction_, header_.base_fee_per_gas.value_or(0));
        intx::be::store(result.tx_gas_price.bytes, gas_cost);

        TTraits::populate_chain_id(result);

        uint256_t const block_base_fee{header_.base_fee_per_gas.value_or(0)};
        intx::be::store(result.block_base_fee.bytes, block_base_fee);

        if (header_.difficulty == 0) { // EIP-4399
            std::memcpy(
                result.block_prev_randao.bytes,
                header_.prev_randao.bytes,
                sizeof(header_.prev_randao.bytes));
        }
        else {
            intx::be::store(result.block_prev_randao.bytes, header_.difficulty);
        }

        return result;
    }

    virtual bytes32_t
    get_block_hash(int64_t const block_number) const noexcept override
    {
        MONAD_DEBUG_ASSERT(block_number >= 0);
        return block_hash_buffer_.get(static_cast<uint64_t>(block_number));
    };

    virtual void emit_log(
        address_t const &address, uint8_t const *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) noexcept override
    {
        Receipt::Log log{.data = {data, data_size}, .address = address};
        for (auto i = 0u; i < num_topics; ++i) {
            log.topics.push_back({topics[i]});
        }
        state_.store_log(std::move(log));
    }

    virtual evmc_access_status
    access_account(address_t const &address) noexcept override
    {
        if (is_precompile<TTraits>(address)) {
            return EVMC_ACCESS_WARM;
        }
        return state_.access_account(address);
    }

    virtual evmc_access_status access_storage(
        address_t const &address, bytes32_t const &key) noexcept override
    {
        return state_.access_storage(address, key);
    }
};

MONAD_EXECUTION_NAMESPACE_END
