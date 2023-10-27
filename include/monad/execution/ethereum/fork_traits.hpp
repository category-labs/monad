#pragma once

#include <monad/config.hpp>

#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/transaction.hpp>

#include <monad/execution/ethereum/dao.hpp>

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
        Block const &block, uint256_t const &reward,
        uint256_t const &ommer_reward)
    {
        MONAD_DEBUG_ASSERT(
            reward + intx::umul(ommer_reward, uint256_t{block.ommers.size()}) <=
            std::numeric_limits<uint256_t>::max());
        return reward + ommer_reward * block.ommers.size();
    }

    static constexpr uint256_t calculate_ommer_award(
        Block const &block, uint256_t const &reward, uint64_t ommer_number)
    {
        auto const subtrahend =
            ((block.header.number - ommer_number) * reward) / 8;
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
        g_data(Transaction const &txn) noexcept
        {
            auto const zeros = std::count_if(
                std::cbegin(txn.data),
                std::cend(txn.data),
                [](unsigned char c) { return c == 0x00; });
            auto const nonzeros =
                txn.data.size() - static_cast<uint64_t>(zeros);
            return static_cast<uint64_t>(zeros) * 4u + nonzeros * 68u;
        }

        // YP, section 6.2, Eqn. 60
        [[nodiscard]] static constexpr uint64_t
        intrinsic_gas(Transaction const &txn) noexcept
        {
            return 21'000 + g_data(txn);
        }

        template <class TState>
        static evmc::Result deploy_contract_code(
            TState &state, address_t const &address,
            evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            auto const deploy_cost =
                static_cast<int64_t>(result.output_size) * 200;
            result.create_address = address;

            if (result.gas_left < deploy_cost) {
                // From YP: "No code is deposited in the state if the gas
                // does not cover the additional per-byte contract deposit
                // fee, however, the value is still transferred and the
                // execution side- effects take place."
                state.set_code(address, {});
            }
            else {
                state.set_code(
                    address, {result.output_data, result.output_size});
                result.gas_left -= deploy_cost;
            }
            return result;
        }

        static constexpr uint256_t gas_price(
            Transaction const &txn, uint256_t const & /*base_fee_per_gas*/)
        {
            return txn.max_fee_per_gas;
        }

        template <class TBlockState>
        static constexpr void apply_block_award_impl(
            TBlockState &block_state, Db &db, Block const &block,
            uint256_t const &reward, uint256_t const &ommer_reward)
        {
            state::State state{block_state, db};
            auto const miner_award =
                calculate_block_award(block, reward, ommer_reward);

            // reward block beneficiary, YP Eqn. 172
            state.add_to_balance(block.header.beneficiary, miner_award);

            // reward ommers, YP Eqn. 175
            for (auto const &header : block.ommers) {
                state.add_to_balance(
                    header.beneficiary,
                    calculate_ommer_award(block, reward, header.number));
            }

            MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
            merge(block_state.state, state.state_);
        }

        template <class TBlockState>
        static constexpr void
        apply_block_award(TBlockState &block_state, Db &db, Block const &block)
        {
            apply_block_award_impl(
                block_state, db, block, block_reward, additional_ommer_reward);
        }

        static constexpr uint256_t calculate_txn_award(
            Transaction const &txn, uint256_t const &base_fee_per_gas,
            uint64_t const gas_used)
        {
            return uint256_t{gas_used} * gas_price(txn, base_fee_per_gas);
        }

        template <class TBlockState>
        static constexpr void
        transfer_balance_dao(TBlockState &, Db &, block_num_t)
        {
        }

        static constexpr void
        populate_chain_id(evmc_tx_context &context) noexcept
        {
            intx::be::store(context.chain_id.bytes, uint256_t{1});
        }
    };

    struct homestead : public frontier
    {
        using next_fork_t = dao_fork;

        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr evmc_revision rev = EVMC_HOMESTEAD;
        static constexpr auto last_block_number = 1'919'999u;

        [[nodiscard]] static constexpr auto
        g_txcreate(Transaction const &txn) noexcept
        {
            if (!txn.to.has_value()) {
                return 32'000u;
            }
            return 0u;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &txn) noexcept
        {
            return g_txcreate(txn) + 21'000u + g_data(txn);
        }

        template <class TState>
        static evmc::Result deploy_contract_code(
            TState &state, address_t const &address,
            evmc::Result result) noexcept
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
                result.create_address = address;
                result.gas_left -= deploy_cost;
                state.set_code(
                    address, {result.output_data, result.output_size});
            }
            return result;
        }
    };

    struct dao_fork : public homestead
    {
        using next_fork_t = tangerine_whistle;
        static constexpr auto last_block_number = 2'462'999u;
        // EVMC revision for DAO should just be EVMC_HOMESTEAD

        template <class TBlockState>
        static constexpr void transfer_balance_dao(
            TBlockState &block_state, Db &db, block_num_t const block_number)
        {
            state::State state{block_state, db};
            if (MONAD_UNLIKELY(
                    block_number == execution::dao::dao_block_number)) {
                for (auto const &addr : execution::dao::child_accounts) {
                    auto const balance =
                        intx::be::load<uint256_t>(state.get_balance(addr));
                    state.add_to_balance(
                        execution::dao::withdraw_account, balance);
                    state.subtract_from_balance(addr, balance);
                }

                MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
                merge(block_state.state, state.state_);
            }
        }
    };

    struct tangerine_whistle : public dao_fork
    {
        using next_fork_t = spurious_dragon;

        static constexpr auto last_block_number = 2'674'999u;
        static constexpr evmc_revision rev = EVMC_TANGERINE_WHISTLE;

        template <class TBlockState>
        static constexpr void
        transfer_balance_dao(TBlockState &, Db &, block_num_t)
        {
        }
    };

    struct spurious_dragon : public tangerine_whistle
    {
        using next_fork_t = byzantium;

        static constexpr evmc_revision rev = EVMC_SPURIOUS_DRAGON;
        static constexpr auto last_block_number = 4'369'999u;
        static constexpr size_t max_code_size = 0x6000; // EIP-170

        template <class TState>
        [[nodiscard]] static evmc::Result deploy_contract_code(
            TState &state, address_t const &address,
            evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            // EIP-170
            if (result.output_size > max_code_size) {
                return evmc::Result{EVMC_OUT_OF_GAS};
            }
            return homestead::deploy_contract_code(
                state, address, std::move(result));
        }

        template <class TBlockState>
        static constexpr void apply_block_award_impl(
            TBlockState &block_state, Db &db, Block const &block,
            uint256_t const &reward, uint256_t const &ommer_reward)
        {
            state::State state{block_state, db};
            auto const miner_reward =
                calculate_block_award(block, reward, ommer_reward);

            // reward block beneficiary, YP Eqn. 172
            if (miner_reward) {
                state.add_to_balance(block.header.beneficiary, miner_reward);
            }

            // reward ommers, YP Eqn. 175
            for (auto const &header : block.ommers) {
                auto const ommer_reward =
                    calculate_ommer_award(block, reward, header.number);
                if (ommer_reward) {
                    state.add_to_balance(header.beneficiary, ommer_reward);
                }
            }

            MONAD_DEBUG_ASSERT(can_merge(block_state.state, state.state_));
            merge(block_state.state, state.state_);
        }

        template <class TBlockState>
        static constexpr void
        apply_block_award(TBlockState &block_state, Db &db, Block const &block)
        {
            apply_block_award_impl(
                block_state, db, block, block_reward, additional_ommer_reward);
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

        template <class TBlockState>
        static constexpr void
        apply_block_award(TBlockState &block_state, Db &db, Block const &block)
        {
            apply_block_award_impl(
                block_state, db, block, block_reward, additional_ommer_reward);
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

        template <class TBlockState>
        static constexpr void
        apply_block_award(TBlockState &block_state, Db &db, Block const &block)
        {
            apply_block_award_impl(
                block_state, db, block, block_reward, additional_ommer_reward);
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
        g_data(Transaction const &txn) noexcept
        {
            auto const zeros = std::count_if(
                std::cbegin(txn.data),
                std::cend(txn.data),
                [](unsigned char c) { return c == 0x00; });
            auto const nonzeros =
                txn.data.size() - static_cast<uint64_t>(zeros);
            return static_cast<uint64_t>(zeros) * 4u + nonzeros * 16u;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &txn) noexcept
        {
            return g_txcreate(txn) + 21'000u + g_data(txn);
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
        g_access_and_storage(Transaction const &txn) noexcept
        {
            uint64_t g = txn.access_list.size() * 2'400u;
            for (auto &i : txn.access_list) {
                g += i.keys.size() * 1'900u;
            }
            return g;
        }

        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &txn) noexcept
        {
            return g_txcreate(txn) + 21'000u + g_data(txn) +
                   g_access_and_storage(txn);
        }
    };

    struct london : public berlin
    {
        using next_fork_t = paris;

        static constexpr evmc_revision rev = EVMC_LONDON;
        static constexpr auto last_block_number = 15'537'393u;

        // https://eips.ethereum.org/EIPS/eip-3541
        template <class TState>
        [[nodiscard]] static evmc::Result deploy_contract_code(
            TState &state, address_t const &address,
            evmc::Result result) noexcept
        {
            MONAD_DEBUG_ASSERT(result.status_code == EVMC_SUCCESS);
            if (result.output_size > 0 && result.output_data[0] == 0xef) {
                return evmc::Result{EVMC_CONTRACT_VALIDATION_FAILURE};
            }
            return berlin::deploy_contract_code(
                state, address, std::move(result));
        }

        // https://eips.ethereum.org/EIPS/eip-1559
        static constexpr uint256_t
        gas_price(Transaction const &txn, uint256_t const &base_fee_per_gas)
        {
            return priority_fee_per_gas(txn, base_fee_per_gas) +
                   base_fee_per_gas;
        }

        static constexpr uint256_t priority_fee_per_gas(
            Transaction const &txn, uint256_t const &base_fee_per_gas)
        {
            MONAD_DEBUG_ASSERT(txn.max_fee_per_gas >= base_fee_per_gas);
            if (txn.type == TransactionType::eip1559) {
                return std::min(
                    txn.max_priority_fee_per_gas,
                    txn.max_fee_per_gas - base_fee_per_gas);
            }
            // per eip-1559: "Legacy Ethereum transactions will still work and
            // be included in blocks, but they will not benefit directly from
            // the new pricing system. This is due to the fact that upgrading
            // from legacy transactions to new transactions results in the
            // legacy transaction’s gas_price entirely being consumed either
            // by the base_fee_per_gas and the priority_fee_per_gas."
            return txn.max_fee_per_gas - base_fee_per_gas;
        }

        static constexpr uint256_t calculate_txn_award(
            Transaction const &txn, uint256_t const &base_fee_per_gas,
            uint64_t const gas_used)
        {
            return gas_used * priority_fee_per_gas(txn, base_fee_per_gas);
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

        template <class TBlockState>
        static constexpr void
        apply_block_award(TBlockState &block_state, Db &db, Block const &block)
        {
            apply_block_award_impl(
                block_state, db, block, block_reward, additional_ommer_reward);
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

        // EIP-3860
        [[nodiscard]] static constexpr uint64_t
        g_extra_cost_init(Transaction const &txn) noexcept
        {
            if (!txn.to.has_value()) {
                return ((txn.data.length() + 31u) / 32u) * 2u;
            }
            return 0u;
        }

        // EIP-3860
        [[nodiscard]] static constexpr auto
        intrinsic_gas(Transaction const &txn) noexcept
        {
            return g_txcreate(txn) + 21'000u + g_data(txn) +
                   g_access_and_storage(txn) + g_extra_cost_init(txn);
        }
    };
}

MONAD_NAMESPACE_END
