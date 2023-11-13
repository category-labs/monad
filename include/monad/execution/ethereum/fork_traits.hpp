#pragma once

#include <monad/config.hpp>

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>

MONAD_NAMESPACE_BEGIN

// https://ethereum.org/en/history/
namespace fork_traits
{
    struct frontier;
    struct homestead;
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

    struct frontier
    {
        using next_fork_t = homestead;

        static constexpr evmc_revision rev = EVMC_FRONTIER;
        static constexpr auto last_block_number = 1'149'999u;
        static constexpr uint256_t block_reward =
            5'000'000'000'000'000'000; // YP Eqn. 176
        static constexpr uint256_t additional_ommer_reward =
            block_reward >> 5; // YP Eqn. 172, block reward / 32
    };

    struct homestead : public frontier
    {
        using next_fork_t = tangerine_whistle;

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
    };

    struct istanbul : public constantinople_and_petersburg
    {
        using next_fork_t = berlin;

        static constexpr evmc_revision rev = EVMC_ISTANBUL;
        static constexpr auto last_block_number = 12'243'999u;
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
    };

    struct shanghai : public paris
    {
        using next_fork_t = no_next_fork_t;
        static constexpr evmc_revision rev = EVMC_SHANGHAI;
        static constexpr auto last_block_number =
            std::numeric_limits<uint64_t>::max();
    };
}

MONAD_NAMESPACE_END
