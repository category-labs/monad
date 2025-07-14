#pragma once

#include <monad/vm/runtime/uint256.hpp>

#include <bit>

namespace monad::vm::utils::evm_as
{
    template <typename T>
        requires requires(T const &x) {
            static_cast<size_t>(runtime::bit_width(x));
        }

    inline size_t byte_width(T imm)
    {
        return (static_cast<size_t>(runtime::bit_width(imm)) + 7) / 8;
    }
}
