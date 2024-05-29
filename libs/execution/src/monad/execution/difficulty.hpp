#pragma once

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/int.hpp>

#include <evmc/evmc.hpp>

MONAD_NAMESPACE_BEGIN

template <evmc_revision rev>
uint256_t
difficulty(BlockHeader const &header, BlockHeader const &parent_header)
{
    uint256_t difficulty{parent_header.difficulty};
    uint256_t delta{parent_header.difficulty >> 11};
    int multiplier{0};

    MONAD_DEBUG_ASSERT(header.timestamp > parent_header.timestamp);
    auto const time_diff = header.timestamp - parent_header.timestamp;

    if constexpr (rev == EVMC_FRONTIER) {
        multiplier = time_diff >= 13 ? -1 : 1;
    }
    else if constexpr (rev < EVMC_BYZANTIUM) {
        // EIP-2
        // We flip the sign here to avoid underflow of unsigned integer
        multiplier =
            1 -
            (time_diff / 10 >= 100 ? 100 : static_cast<int>(time_diff / 10));
    }
    else {
        // EIP-100
        if (parent_header.ommers_hash != NULL_LIST_HASH) {
            multiplier =
                2 -
                (time_diff / 9 >= 101 ? 101 : static_cast<int>(time_diff / 9));
        }
        else {
            multiplier =
                1 -
                (time_diff / 9 >= 100 ? 100 : static_cast<int>(time_diff / 9));
        }
    }

    if (multiplier >= 0) {
        difficulty += delta * multiplier;
    }
    else {
        difficulty -= delta * abs(multiplier);
    }

    // TODO: We don't implement certain bomb delay now, as it relates to config
    // file
    uint64_t bomb_delay{0};
    uint64_t block_number{header.number};
    if (rev >= EVMC_LONDON) {
        // EIP-3554
        bomb_delay = 9'700'000;
    }
    else if (rev >= EVMC_CONSTANTINOPLE) {
        // EIP-1234
        bomb_delay = 5'000'000;
    }
    else if (rev >= EVMC_BYZANTIUM) {
        // EIP-649
        bomb_delay = 3'000'000;
    }

    if (MONAD_LIKELY(block_number > bomb_delay)) {
        block_number -= bomb_delay;
    }
    else {
        block_number = 0;
    }

    uint256_t adjustment{0};

    if (MONAD_LIKELY(block_number / 100'000 >= 2)) {
        adjustment = uint256_t{1} << (block_number / 100'000 - 2);
    }

    difficulty += adjustment;

    static constexpr uint64_t min_diff{0x20000};
    if (MONAD_UNLIKELY(difficulty < min_diff)) {
        difficulty = min_diff;
    }

    return difficulty;
}

MONAD_NAMESPACE_END
