#pragma once

#include <monad/config.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>

#include <monad/execution/ethereum/dao.hpp>

#include <monad/db/block_db.hpp>
#include <monad/db/db.hpp>

#include <monad/state2/state.hpp>

#include <evmc/evmc.h>

#include <algorithm>

#include <boost/mp11/mpl_list.hpp>

MONAD_NAMESPACE_BEGIN

// https://ethereum.org/en/history/
namespace fork_traits
{
    struct frontier;
    struct homestead;
    struct dao_fork;
    struct tangerine_whistle;
    struct spurious_dragon;
    struct byzantium;
    struct constantinople_and_petersburg;
    struct istanbul;
    struct berlin;
    struct london;
    struct paris;
    struct shanghai;

    using no_next_fork_t = shanghai;

    static constexpr uint256_t calculate_block_award(
        Block const &b, uint256_t const &reward, uint256_t const &ommer_reward,
        uint256_t const &gas_award)
    {
        return reward + ommer_reward * b.ommers.size() + gas_award;
    }

    static constexpr uint256_t calculate_ommer_award(
        Block const &b, uint256_t const &reward, uint64_t ommer_number)
    {
        auto const subtrahend = ((b.header.number - ommer_number) * reward) / 8;
        return reward - subtrahend;
    }

    struct frontier
    {
        using next_fork_t = homestead;

        static constexpr evmc_revision rev = EVMC_FRONTIER;
        static constexpr auto last_block_number = 1'149'999u;
        static constexpr uint256_t block_reward =
            5'000'000'000'000'000'000; // YP Eqn. 176
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32

        static constexpr uint64_t n_precompiles = 4;

        // YP, Eqn. 60, first summation
        [[nodiscard]] static constexpr uint64_t
        g_data(Transaction const &t) noexcept
        {
            auto const zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            auto const nonzeros = t.data.size() - static_cast<uint64_t>(zeros);
            return static_cast<uint64_t>(zeros) * 4u + nonzeros * 68u;
        }

        // YP, section 6.2, Eqn. 60
        [[nodiscard]] static constexpr uint64_t
        intrinsic_gas(Transaction const &t) noexcept
        {
            return 21'000 + g_data(t);
        }

        [[nodiscard]] static constexpr auto starting_nonce() noexcept
        {
            return 0u;
        }

        [[nodiscard]] static constexpr uint64_t max_refund_quotient() noexcept
        {
            return 2u;
        }

        template <class TState>
        static constexpr void destruct_touched_dead(TState &) noexcept
        {
        }

        template <class TState>
        static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            auto const deploy_cost =
                static_cast<int64_t>(result.output_size) * 200;
            result.create_address = a;

            if (result.gas_left < deploy_cost) {
                // From YP: "No code is deposited in the state if the gas
                // does not cover the additional per-byte contract deposit
                // fee, however, the value is still transferred and the
                // execution side- effects take place."
                s.set_code(a, {});
            }
            else {
                s.set_code(a, {result.output_data, result.output_size});
                result.gas_left -= deploy_cost;
            }
            return result;
        }

        static constexpr uint256_t
        gas_price(Transaction const &t, uint256_t const & /*base_fee_per_gas*/)
        {
            return t.max_fee_per_gas;
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award_impl(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &reward,
            uint256_t const &ommer_reward, uint256_t const &gas_award)
        {
            state::State s{bs, db, block_cache};
            auto const miner_award =
                calculate_block_award(b, reward, ommer_reward, gas_award);

            // reward block beneficiary, YP Eqn. 172
            s.add_to_balance(b.header.beneficiary, miner_award);

            // reward ommers, YP Eqn. 175
            for (auto const &header : b.ommers) {
                s.add_to_balance(
                    header.beneficiary,
                    calculate_ommer_award(b, reward, header.number));
            }

            MONAD_DEBUG_ASSERT(can_merge(bs.state, s.state_));
            merge(bs.state, s.state_);
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &gas_award)
        {
            apply_block_award_impl(
                bs,
                db,
                block_cache,
                b,
                block_reward,
                additional_ommer_reward,
                gas_award);
        }

        static constexpr uint256_t calculate_txn_award(
            Transaction const &t, uint256_t const &base_fee_per_gas,
            uint64_t gas_used)
        {
            return uint256_t{gas_used} * gas_price(t, base_fee_per_gas);
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void transfer_balance_dao(
            TBlockState &, Db &, TBlockCache const &, block_num_t const)
        {
        }

        static constexpr void validate_block(Block const &) {}

        template <typename TState>
        static constexpr void warm_coinbase(TState &, address_t const &)
        {
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void process_withdrawal(
            TBlockState &, Db &, TBlockCache const &,
            std::optional<std::vector<Withdrawal>> const &)
        {
        }

        template <class TState>
        [[nodiscard]] static constexpr bool
        account_exists(TState &state, address_t const &address)
        {
            return state.account_exists(address);
        }

        static constexpr void
        populate_chain_id(evmc_tx_context &context) noexcept
        {
            intx::be::store(context.chain_id.bytes, uint256_t{1});
        }

        [[nodiscard]] static constexpr bool
        transaction_type_valid(TransactionType const type)
        {
            return type == TransactionType::eip155;
        }

        [[nodiscard]] static constexpr bool
        init_code_valid(Transaction const &) noexcept
        {
            return true;
        }

        [[nodiscard]] static constexpr bool
        chain_id_valid(Transaction const &txn)
        {
            return !txn.sc.chain_id.has_value();
        }
    };

    struct homestead : public frontier
    {
        using next_fork_t = dao_fork;

        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr evmc_revision rev = EVMC_HOMESTEAD;
        static constexpr auto last_block_number = 1'919'999u;

        [[nodiscard]] static constexpr auto
        g_txcreate(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                return 32'000u;
            }
            return 0u;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t);
        }

        template <class TState>
        static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            auto const deploy_cost =
                static_cast<int64_t>(result.output_size) * 200;

            if (result.gas_left < deploy_cost) {
                // EIP-2: If contract creation does not have enough gas to
                // pay for the final gas fee for adding the contract code to
                // the state, the contract creation fails (ie. goes
                // out-of-gas) rather than leaving an empty contract.
                result.status_code = EVMC_OUT_OF_GAS;
            }
            else {
                result.create_address = a;
                result.gas_left -= deploy_cost;
                s.set_code(a, {result.output_data, result.output_size});
            }
            return result;
        }
    };

    struct dao_fork : public homestead
    {
        using next_fork_t = tangerine_whistle;
        static constexpr auto last_block_number = 2'462'999u;
        // EVMC revision for DAO should just be EVMC_HOMESTEAD

        template <class TBlockState, class TBlockCache>
        static constexpr void transfer_balance_dao(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            block_num_t const block_number)
        {
            state::State s{bs, db, block_cache};
            if (MONAD_UNLIKELY(
                    block_number == execution::dao::dao_block_number)) {
                for (auto const &addr : execution::dao::child_accounts) {
                    auto const balance =
                        intx::be::load<uint256_t>(s.get_balance(addr));
                    s.add_to_balance(execution::dao::withdraw_account, balance);
                    s.subtract_from_balance(addr, balance);
                }

                MONAD_DEBUG_ASSERT(can_merge(bs.state, s.state_));
                merge(bs.state, s.state_);
            }
        }
    };

    struct tangerine_whistle : public dao_fork
    {
        using next_fork_t = spurious_dragon;

        static constexpr auto last_block_number = 2'674'999u;
        static constexpr evmc_revision rev = EVMC_TANGERINE_WHISTLE;

        template <class TBlockState, class TBlockCache>
        static constexpr void transfer_balance_dao(
            TBlockState &, Db &, TBlockCache const &, block_num_t const block)
        {
            MONAD_DEBUG_ASSERT(block > dao_fork::last_block_number);
        }
    };

    struct spurious_dragon : public tangerine_whistle
    {
        using next_fork_t = byzantium;

        static constexpr evmc_revision rev = EVMC_SPURIOUS_DRAGON;
        static constexpr auto last_block_number = 4'369'999u;
        static constexpr size_t max_code_size = 0x6000; // EIP-170

        // https://eips.ethereum.org/EIPS/eip-161
        [[nodiscard]] static constexpr auto starting_nonce() noexcept
        {
            return 1u;
        }

        template <class TState>
        static constexpr void destruct_touched_dead(TState &s) noexcept
        {
            s.destruct_touched_dead();
        }

        template <class TState>
        [[nodiscard]] static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            // EIP-170
            if (result.output_size > max_code_size) {
                return evmc::Result{EVMC_OUT_OF_GAS};
            }
            return homestead::deploy_contract_code(s, a, std::move(result));
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award_impl(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &reward,
            uint256_t const &ommer_reward, uint256_t const &gas_award)
        {
            state::State s{bs, db, block_cache};
            auto const miner_reward =
                calculate_block_award(b, reward, ommer_reward, gas_award);

            // reward block beneficiary, YP Eqn. 172
            if (miner_reward) {
                s.add_to_balance(b.header.beneficiary, miner_reward);
            }

            // reward ommers, YP Eqn. 175
            for (auto const &header : b.ommers) {
                auto const ommer_reward =
                    calculate_ommer_award(b, reward, header.number);
                if (ommer_reward) {
                    s.add_to_balance(header.beneficiary, ommer_reward);
                }
            }

            MONAD_DEBUG_ASSERT(can_merge(bs.state, s.state_));
            merge(bs.state, s.state_);
        }

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &gas_award)
        {
            apply_block_award_impl(
                bs,
                db,
                block_cache,
                b,
                block_reward,
                additional_ommer_reward,
                gas_award);
        }

        template <class TState>
        [[nodiscard]] static constexpr bool
        account_exists(TState &state, address_t const &address)
        {
            return !state.account_is_dead(address);
        }

        [[nodiscard]] static constexpr bool
        chain_id_valid(Transaction const &txn)
        {
            return !txn.sc.chain_id.has_value() || txn.sc.chain_id.value() == 1;
        }
    };

    struct byzantium : public spurious_dragon
    {
        using next_fork_t = constantinople_and_petersburg;

        static constexpr evmc_revision rev = EVMC_BYZANTIUM;
        static constexpr auto last_block_number = 7'279'999u;
        static constexpr uint256_t block_reward =
            3'000'000'000'000'000'000; // YP Eqn. 176, EIP-649
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32

        static constexpr uint64_t n_precompiles = 8;

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &gas_award)
        {
            apply_block_award_impl(
                bs,
                db,
                block_cache,
                b,
                block_reward,
                additional_ommer_reward,
                gas_award);
        }
    };

    // EIP-1716 petersburg and constantinople forks are activated at the same
    // block on mainnet
    struct constantinople_and_petersburg : public byzantium
    {
        using next_fork_t = istanbul;

        static constexpr evmc_revision rev = EVMC_PETERSBURG;
        static constexpr auto last_block_number = 9'068'999;
        static constexpr uint256_t block_reward =
            2'000'000'000'000'000'000; // YP Eqn. 176, EIP-1234
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &gas_award)
        {
            apply_block_award_impl(
                bs,
                db,
                block_cache,
                b,
                block_reward,
                additional_ommer_reward,
                gas_award);
        }
    };

    struct istanbul : public constantinople_and_petersburg
    {
        using next_fork_t = berlin;

        static constexpr evmc_revision rev = EVMC_ISTANBUL;
        static constexpr auto last_block_number = 12'243'999u;

        static constexpr uint64_t n_precompiles = 9;

        // https://eips.ethereum.org/EIPS/eip-2028
        [[nodiscard]] static constexpr uint64_t
        g_data(Transaction const &t) noexcept
        {
            auto const zeros = std::count_if(
                std::cbegin(t.data), std::cend(t.data), [](unsigned char c) {
                    return c == 0x00;
                });
            auto const nonzeros = t.data.size() - static_cast<uint64_t>(zeros);
            return static_cast<uint64_t>(zeros) * 4u + nonzeros * 16u;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t);
        }
    };

    // muir_glacier - 9'200'000

    struct berlin : public istanbul
    {
        using next_fork_t = london;

        static constexpr evmc_revision rev = EVMC_BERLIN;
        static constexpr auto last_block_number = 12'964'999u;

        // https://eips.ethereum.org/EIPS/eip-2930
        [[nodiscard]] static constexpr auto
        g_access_and_storage(Transaction const &t) noexcept
        {
            uint64_t g = t.access_list.size() * 2'400u;
            for (auto &i : t.access_list) {
                g += i.keys.size() * 1'900u;
            }
            return g;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t) +
                   g_access_and_storage(t);
        }

        [[nodiscard]] static constexpr bool
        transaction_type_valid(TransactionType const type)
        {
            return type == TransactionType::eip155 ||
                   type == TransactionType::eip2930;
        }
    };

    struct london : public berlin
    {
        using next_fork_t = paris;

        static constexpr evmc_revision rev = EVMC_LONDON;
        static constexpr auto last_block_number = 15'537'393u;

        // https://eips.ethereum.org/EIPS/eip-3529
        [[nodiscard]] static constexpr uint64_t max_refund_quotient() noexcept
        {
            return 5u;
        }

        // https://eips.ethereum.org/EIPS/eip-3541
        template <class TState>
        [[nodiscard]] static evmc::Result deploy_contract_code(
            TState &s, address_t const &a, evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            if (result.output_size > 0 && result.output_data[0] == 0xef) {
                return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
            }
            return berlin::deploy_contract_code(s, a, std::move(result));
        }

        // https://eips.ethereum.org/EIPS/eip-1559
        static constexpr uint256_t
        gas_price(Transaction const &t, uint256_t const &base_fee_per_gas)
        {
            return priority_fee_per_gas(t, base_fee_per_gas) + base_fee_per_gas;
        }

        static constexpr uint256_t priority_fee_per_gas(
            Transaction const &t, uint256_t const &base_fee_per_gas)
        {
            MONAD_DEBUG_ASSERT(t.max_fee_per_gas >= base_fee_per_gas);
            if (t.type == TransactionType::eip1559) {
                return std::min(
                    t.max_priority_fee_per_gas,
                    t.max_fee_per_gas - base_fee_per_gas);
            }
            // per eip-1559: "Legacy Ethereum transactions will still work and
            // be included in blocks, but they will not benefit directly from
            // the new pricing system. This is due to the fact that upgrading
            // from legacy transactions to new transactions results in the
            // legacy transaction’s gas_price entirely being consumed either by
            // the base_fee_per_gas and the priority_fee_per_gas."
            return t.max_fee_per_gas - base_fee_per_gas;
        }

        static constexpr uint256_t calculate_txn_award(
            Transaction const &t, uint256_t const &base_fee_per_gas,
            uint64_t gas_used)
        {
            return gas_used * priority_fee_per_gas(t, base_fee_per_gas);
        }

        [[nodiscard]] static constexpr bool
        transaction_type_valid(TransactionType const type)
        {
            return type == TransactionType::eip155 ||
                   type == TransactionType::eip2930 ||
                   type == TransactionType::eip1559;
        }
    };

    struct paris : public london
    {
        using next_fork_t = shanghai;
        static constexpr evmc_revision rev = EVMC_PARIS;
        static constexpr auto last_block_number = 17'034'869u;

        // EIP-3675
        static constexpr uint256_t block_reward = 0;
        static constexpr uint256_t additional_ommer_reward = 0;

        template <class TBlockState, class TBlockCache>
        static constexpr void apply_block_award(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            Block const &b, uint256_t const &gas_award)
        {
            apply_block_award_impl(
                bs,
                db,
                block_cache,
                b,
                block_reward,
                additional_ommer_reward,
                gas_award);
        }

        static constexpr void validate_block(Block const &b)
        {
            MONAD_DEBUG_ASSERT(b.header.ommers_hash == NULL_LIST_HASH);
            MONAD_DEBUG_ASSERT(b.header.difficulty == 0u);
            byte_string_fixed<8> empty{
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
            MONAD_DEBUG_ASSERT(b.header.nonce == empty);
            MONAD_DEBUG_ASSERT(b.ommers.size() == 0u);
            MONAD_DEBUG_ASSERT(b.header.extra_data.length() <= 32u);
        }
    };

    struct shanghai : public paris
    {
        using next_fork_t = no_next_fork_t;
        static constexpr evmc_revision rev = EVMC_SHANGHAI;
        static constexpr auto last_block_number =
            std::numeric_limits<uint64_t>::max();
        static constexpr size_t max_init_code_size =
            2 * max_code_size; // EIP-3860

        // EIP-3651
        template <class TState>
        static constexpr void
        warm_coinbase(TState &s, address_t const &beneficiary)
        {
            s.warm_coinbase(beneficiary);
        }

        // EIP-3860
        [[nodiscard]] static constexpr uint64_t
        g_extra_cost_init(Transaction const &t) noexcept
        {
            if (!t.to.has_value()) {
                return ((t.data.length() + 31u) / 32u) * 2u;
            }
            return 0u;
        }

        // EIP-3860
        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &t) noexcept
        {
            return g_txcreate(t) + 21'000u + g_data(t) +
                   g_access_and_storage(t) + g_extra_cost_init(t);
        }

        // EIP-4895
        template <class TBlockState, class TBlockCache>
        static constexpr void process_withdrawal(
            TBlockState &bs, Db &db, TBlockCache const &block_cache,
            std::optional<std::vector<Withdrawal>> const &withdrawals)
        {
            if (withdrawals.has_value()) {
                state::State s{bs, db, block_cache};
                for (auto const &withdrawal : withdrawals.value()) {
                    s.add_to_balance(
                        withdrawal.recipient,
                        uint256_t{withdrawal.amount} *
                            uint256_t{1'000'000'000u});
                }

                MONAD_DEBUG_ASSERT(can_merge(bs.state, s.state_));
                merge(bs.state, s.state_);
            }
        }

        // EIP-3860
        [[nodiscard]] static constexpr bool
        init_code_valid(Transaction const &txn) noexcept
        {
            if (!txn.to.has_value()) {
                return txn.data.size() <= max_init_code_size;
            }
            // this is not contract creation
            return true;
        }
    };
}

MONAD_NAMESPACE_END
