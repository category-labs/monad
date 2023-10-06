#pragma once

#include <monad/config.hpp>

#include <optional>

MONAD_NAMESPACE_BEGIN

struct Configuration
{
    std::optional<uint64_t> homestead_block;
    std::optional<uint64_t> dao_block;
    std::optional<uint64_t> tangerine_whistle_block;
    std::optional<uint64_t> spurious_dragon_block;
    std::optional<uint64_t> byzantium_block;
    std::optional<uint64_t> constantinople_and_petersburg_block;
    std::optional<uint64_t> istanbul_block;
    std::optional<uint64_t> berlin_block;
    std::optional<uint64_t> london_block;
    std::optional<uint64_t> paris_block;
    std::optional<uint64_t> shanghai_block;
};

constexpr auto ethereum_mainnet_config = Configuration{
    .homestead_block = 1'150'000,
    .dao_block = 1'920'000,
    .tangerine_whistle_block = 2'463'000,
    .spurious_dragon_block = 2'675'000,
    .byzantium_block = 4'370'000,
    .constantinople_and_petersburg_block = 7'280'000,
    .istanbul_block = 9'069'000,
    .berlin_block = 1'224'4000,
    .london_block = 12'965'000,
    .paris_block = 15'537'394,
    .shanghai_block = 17'034'870};

MONAD_NAMESPACE_END
