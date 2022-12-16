#pragma once

#include <monad/config.hpp>
#include <monad/mpt/nibble.hpp>
#include <cstdint>
#include <initializer_list>
#include <algorithm>

MONAD_NAMESPACE_BEGIN

namespace tests_utils
{
constexpr auto to_bytes(std::initializer_list<uint8_t> list)
{
    return monad::byte_string(list);
}

constexpr auto to_nibbles(std::initializer_list<uint8_t> list)
{
    monad::mpt::Nibbles nibbles; 
    std::ranges::transform(list, std::back_inserter(nibbles), [](auto element) {
        assert((element & 0xf0) == 0);
        return monad::mpt::Nibble{element};
    });
    return nibbles;
}
} // namespace tests_utils

MONAD_NAMESPACE_END
