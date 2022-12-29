#pragma once

#include <cstdint>
#include <initializer_list>
#include <algorithm>

#include <monad/config.hpp>
#include <monad/mpt/nibble.hpp>

#include <range/v3/view/transform.hpp>
#include <range/v3/range/conversion.hpp>

MONAD_NAMESPACE_BEGIN

namespace test_util
{
inline auto to_nibbles(std::initializer_list<uint8_t> list)
{
    return list | ranges::to<monad::mpt::Nibbles>();
}
} // namespace tests_utils

MONAD_NAMESPACE_END
