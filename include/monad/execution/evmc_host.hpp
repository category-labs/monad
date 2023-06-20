#pragma once

#include <monad/core/address.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/concepts.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <intx/intx.hpp>

#include <evmc/evmc.hpp>

#include <utility>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TState, concepts::fork_traits<TState> TTraits, class TEvm>
struct EvmcHost : public evmc::HostInterface
{
    BlockHeader const &block_header_;
    Transaction const &transaction_;
    TState &state_;
    TEvm &evm_;

    using uint256be = evmc::uint256be;

    EvmcHost(
        BlockHeader const &b, Transaction const &t, TState &s, TEvm &e) noexcept
        : block_header_{b}
        , transaction_{t}
        , state_{s}
        , evm_{e}
    {
    }
    virtual ~EvmcHost() noexcept = default;

    virtual bool account_exists(address_t const &a) const noexcept override
    {
        return state_.account_exists(a);
    }

    virtual bytes32_t get_storage(
        const address_t &a, const bytes32_t &key) const noexcept override
    {
        return state_.get_storage(a, key);
    }

    virtual evmc_storage_status set_storage(
        address_t const &a, bytes32_t const &key,
        bytes32_t const &value) noexcept override
    {
        return state_.set_storage(a, key, value);
    }

    virtual uint256be get_balance(address_t const &a) const noexcept override
    {
        return state_.get_balance(a);
    }

    virtual size_t get_code_size(address_t const &a) const noexcept override
    {
        return state_.get_code_size(a);
    }

    virtual bytes32_t get_code_hash(address_t const &a) const noexcept override
    {
        return state_.get_code_hash(a);
    }

    virtual size_t copy_code(
        address_t const &a, size_t offset, uint8_t *data,
        size_t size) const noexcept override
    {
        return state_.copy_code(a, offset, data, size);
    }

    [[nodiscard]] virtual bool selfdestruct(
        address_t const &a, address_t const &beneficiary) noexcept override
    {
        return state_.selfdestruct(a, beneficiary);
    }

    [[nodiscard]] static constexpr evmc_message
    make_msg_from_txn(Transaction const &t)
    {
        const auto to_address = [&] {
            if (t.to) {
                return std::pair{EVMC_CALL, *t.to};
            }
            return std::pair{EVMC_CREATE, address_t{}};
        }();

        evmc_message m{
            .kind = to_address.first,
            .gas =
                static_cast<int64_t>(t.gas_limit - TTraits::intrinsic_gas(t)),
            .recipient = to_address.second,
            .sender = *t.from,
            .input_data = t.data.data(),
            .input_size = t.data.size(),
        };
        uint256_t v{t.amount};
        intx::be::store(m.value.bytes, v);
        return m;
    }

    [[nodiscard]] constexpr Receipt make_receipt_from_result(
        evmc_status_code sc, Transaction const &t, uint64_t const gas_remaining)
    {
        Receipt receipt{
            .status = sc == EVMC_SUCCESS ? 1u : 0u,
            .gas_used = t.gas_limit - gas_remaining,
            .type = t.type,
            .logs = std::move(state_.logs())};
        return receipt;
    }

    [[nodiscard]] virtual evmc::Result
    call(evmc_message const &m) noexcept override
    {
        if (m.kind == EVMC_CREATE || m.kind == EVMC_CREATE2) {
            return evm_.create_contract_account(this, m);
        }

        return evm_.call_evm(this, m);
    }

    virtual evmc_tx_context get_tx_context() const noexcept override
    {
        evmc_tx_context result{
            .tx_origin = *transaction_.from,
            .block_coinbase = block_header_.beneficiary,
            .block_number = static_cast<int64_t>(block_header_.number),
            .block_timestamp = static_cast<int64_t>(block_header_.timestamp),
            .block_gas_limit = static_cast<int64_t>(block_header_.gas_limit)};

        const uint256_t gas_cost = per_gas_cost(
            transaction_, block_header_.base_fee_per_gas.value_or(0));
        intx::be::store(result.tx_gas_price.bytes, gas_cost);

        // Note: is there a better place for us to get the chain_id?
        const uint256_t chain_id = transaction_.sc.chain_id.value_or(0);
        intx::be::store(result.chain_id.bytes, chain_id);

        const uint256_t block_base_fee{
            block_header_.base_fee_per_gas.value_or(0)};
        intx::be::store(result.block_base_fee.bytes, block_base_fee);

        if (block_header_.difficulty == 0) { // EIP-4399
            std::memcpy(
                result.block_prev_randao.bytes,
                block_header_.mix_hash.bytes,
                sizeof(block_header_.mix_hash.bytes));
        }
        else {
            intx::be::store(
                result.block_prev_randao.bytes, block_header_.difficulty);
        }

        return result;
    }

    virtual bytes32_t get_block_hash(
        [[maybe_unused]] int64_t block_number) const noexcept override
    {
        return state_.get_block_hash(block_number);
    };

    virtual void emit_log(
        address_t const &addr, const uint8_t *data, size_t data_size,
        bytes32_t const topics[], size_t num_topics) noexcept override
    {
        Receipt::Log l{.data = {data, data_size}, .address = addr};
        for (auto i = 0u; i < num_topics; ++i) {
            l.topics.push_back({topics[i]});
        }
        state_.store_log(std::move(l));
    }

    virtual evmc_access_status
    access_account(address_t const &a) noexcept override
    {
        return state_.access_account(a);
    }

    virtual evmc_access_status
    access_storage(address_t const &a, bytes32_t const &key) noexcept override
    {
        return state_.access_storage(a, key);
    }
};

MONAD_EXECUTION_NAMESPACE_END
