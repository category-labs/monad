#pragma once

#include <monad/vm/runtime/uint256.hpp>

#include <format>

namespace monad::vm::compiler
{
    using byte_offset = std::size_t;

    using block_id = std::size_t;

    using uint256_t = runtime::uint256_t;

    inline constexpr block_id INVALID_BLOCK_ID =
        std::numeric_limits<block_id>::max();
}
