#pragma once

#include "bytes.hpp"

#include <monad/core/account.hpp>

#include <array>
#include <cstdint>

namespace monad::state_history
{
    struct Account
    {
        using Balance = std::array<uint8_t, monad::uint256_t::num_bits / 8>;

        monad::Account account;

        [[nodiscard]] constexpr Balance get_balance() const noexcept
        {
            // TODO
            return {};
        }

        [[nodiscard]] constexpr uint64_t get_nonce() const noexcept
        {
            // TODO
            return 0;
        }

        [[nodiscard]] Bytes32 get_code_hash() const noexcept
        {
            // TODO
            return {};
        }
    };
}
