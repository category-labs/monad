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

        template <class TBlockState>
        static constexpr void apply_block_award_impl(
            TBlockState &block_state, Db &db, Block const &block,
            uint256_t const &reward, uint256_t const &ommer_reward)
        {
            State state{block_state, db};
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
    };

    struct homestead : public frontier
    {
        using next_fork_t = tangerine_whistle;

        // https://eips.ethereum.org/EIPS/eip-2
        static constexpr evmc_revision rev = EVMC_HOMESTEAD;
        static constexpr auto last_block_number = 2'462'999u;
    };

    struct tangerine_whistle : public homestead
    {
        using next_fork_t = spurious_dragon;

        static constexpr auto last_block_number = 2'674'999u;
        static constexpr evmc_revision rev = EVMC_TANGERINE_WHISTLE;
    };

    struct spurious_dragon : public tangerine_whistle
    {
        using next_fork_t = byzantium;

        static constexpr evmc_revision rev = EVMC_SPURIOUS_DRAGON;
        static constexpr auto last_block_number = 4'369'999u;
        static constexpr size_t max_code_size = 0x6000; // EIP-170

        template <class TBlockState>
        static constexpr void apply_block_award_impl(
            TBlockState &block_state, Db &db, Block const &block,
            uint256_t const &reward, uint256_t const &ommer_reward)
        {
            State state{block_state, db};
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
    };

    // muir_glacier - 9'200'000

    struct berlin : public istanbul
    {
        using next_fork_t = london;

        static constexpr evmc_revision rev = EVMC_BERLIN;
        static constexpr auto last_block_number = 12'964'999u;
    };

    struct london : public berlin
    {
        using next_fork_t = paris;

        static constexpr evmc_revision rev = EVMC_LONDON;
        static constexpr auto last_block_number = 15'537'393u;
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
    };
}

MONAD_NAMESPACE_END
