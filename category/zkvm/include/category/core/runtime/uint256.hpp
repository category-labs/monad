// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// zkVM drop-in replacement for the upstream x86-specific uint256.hpp.
// Wraps intx::uint256 and exposes the same interface that the rest of
// the Monad VM code expects (member functions, free functions, types).
#ifdef MONAD_ZKVM

    #pragma once

    #include <category/vm/core/assert.h>

    #include <intx/intx.hpp>

    #include <algorithm>
    #include <bit>
    #include <climits>
    #include <cstdint>
    #include <cstring>
    #include <limits>
    #include <type_traits>

namespace monad::vm::runtime
{
    // ---------------------------------------------------------------
    // uint256_t — inherits from intx::uint256, adds upstream API
    // ---------------------------------------------------------------

    struct uint256_t : intx::uint256
    {
        using word_type = uint64_t;
        static constexpr auto word_num_bits = sizeof(word_type) * 8;
        static constexpr auto num_bits = 256;
        static constexpr auto num_bytes = num_bits / 8;
        static constexpr auto num_words = num_bits / word_num_bits;

        // Inherit all intx constructors
        using intx::uint256::uint256;

        // Implicit conversion from intx::uint256
        [[gnu::always_inline]]
        constexpr uint256_t(intx::uint256 const &x) noexcept
            : intx::uint256{x}
        {
        }

        // ------ Word / byte access ------

        [[gnu::always_inline]]
        inline uint8_t *as_bytes() noexcept
        {
            return reinterpret_cast<uint8_t *>(this);
        }

        [[gnu::always_inline]]
        inline uint8_t const *as_bytes() const noexcept
        {
            return reinterpret_cast<uint8_t const *>(this);
        }

        // ------ Endian conversion / serialisation ------

        [[gnu::always_inline]]
        inline constexpr uint256_t to_be() const noexcept
        {
            return intx::to_big_endian(
                static_cast<intx::uint256 const &>(*this));
        }

        [[gnu::always_inline]]
        static inline constexpr uint256_t
        load_be(uint8_t const (&bytes)[num_bytes]) noexcept
        {
            return load_le_unsafe(bytes).to_be();
        }

        [[gnu::always_inline]]
        static inline constexpr uint256_t
        load_be_unsafe(uint8_t const *bytes) noexcept
        {
            return load_le_unsafe(bytes).to_be();
        }

        [[gnu::always_inline]]
        static inline constexpr uint256_t
        load_le_unsafe(uint8_t const *bytes) noexcept
        {
            return intx::le::unsafe::load<intx::uint256>(bytes);
        }

        template <typename DstT>
        [[gnu::always_inline]]
        inline DstT store_be() const noexcept
        {
            DstT result;
            static_assert(sizeof(result.bytes) == num_bytes);
            store_be(result.bytes);
            return result;
        }

        [[gnu::always_inline]]
        inline void store_be(uint8_t *dest) const noexcept
        {
            uint256_t const be = to_be();
            std::memcpy(dest, &be, num_bytes);
        }

        // ------ Right-shift type enum (upstream compatibility) ------

        enum class RightShiftType
        {
            Arithmetic,
            Logical
        };
    };

    static_assert(std::is_trivially_copyable_v<uint256_t>);
    static_assert(sizeof(uint256_t) == 32);

    template <uint256_t::RightShiftType type>
    [[gnu::always_inline]]
    inline constexpr uint256_t
    shift_right(uint256_t const &x, uint256_t shift0) noexcept
    {
        if constexpr (type == uint256_t::RightShiftType::Logical) {
            return x >> shift0;
        }
        else {
            // Arithmetic right shift
            int64_t const sign_bit = static_cast<int64_t>(x[3]) &
                                     std::numeric_limits<int64_t>::min();
            uint64_t const fill = static_cast<uint64_t>(sign_bit >> 63);

            if (shift0[3] | shift0[2] | shift0[1] | (shift0[0] >= 256)) {
                return uint256_t{fill, fill, fill, fill};
            }

            auto const shift = static_cast<unsigned>(shift0[0]);
            uint256_t result = x >> uint256_t{shift};
            if (fill && shift > 0) {
                uint256_t mask = ~uint256_t{0};
                mask = mask << uint256_t{256 - shift};
                result = static_cast<intx::uint256 const &>(result) |
                         static_cast<intx::uint256 const &>(mask);
            }
            return result;
        }
    }

    // ---------------------------------------------------------------
    // Byte/bit utilities
    // ---------------------------------------------------------------

    [[gnu::always_inline]]
    inline constexpr size_t countl_zero(uint256_t const &x)
    {
        return intx::clz(static_cast<intx::uint256 const &>(x));
    }

    // ---------------------------------------------------------------
    // Misc free functions expected by upstream VM code
    // ---------------------------------------------------------------

    inline uint256_t
    signextend(uint256_t const &byte_index_256, uint256_t const &x)
    {
        if (byte_index_256 >= 31) {
            return x;
        }
        uint64_t const byte_index = byte_index_256[0];
        uint64_t const word_index = byte_index >> 3;
        uint64_t const word = x[word_index];
        int64_t const signed_word = static_cast<int64_t>(word);
        uint64_t const bit_index = (byte_index & 7) * 8;
        // NOLINTNEXTLINE(bugprone-signed-char-misuse)
        int64_t const signed_byte = static_cast<int8_t>(word >> bit_index);
        uint64_t const upper = static_cast<uint64_t>(signed_byte) << bit_index;
        int64_t const signed_lower =
            signed_word &
            ~(std::numeric_limits<int64_t>::min() >> (63 - bit_index));
        uint64_t const lower = static_cast<uint64_t>(signed_lower);
        uint64_t const sign_bits = static_cast<uint64_t>(signed_byte >> 63);
        uint256_t ret;
        for (uint64_t j = 0; j < word_index; ++j) {
            ret[j] = x[j];
        }
        ret[word_index] = upper | lower;
        for (uint64_t j = word_index + 1; j < 4; ++j) {
            ret[j] = sign_bits;
        }
        return ret;
    }

    [[gnu::always_inline]]
    inline uint256_t sar(uint256_t const &shift, uint256_t const &x)
    {
        return shift_right<uint256_t::RightShiftType::Arithmetic>(x, shift);
    }

    inline uint256_t countr_zero(uint256_t const &x)
    {
        int total_count = 0;
        for (size_t i = 0; i < 4; i++) {
            int const count = std::countr_zero(x[i]);
            total_count += count;
            if (count < 64) {
                return uint256_t{total_count};
            }
        }
        return uint256_t{total_count};
    }

    [[gnu::always_inline]]
    inline constexpr bool slt(uint256_t const &x, uint256_t const &y) noexcept
    {
        auto const x_neg = x[uint256_t::num_words - 1] >> 63;
        auto const y_neg = y[uint256_t::num_words - 1] >> 63;
        auto const diff = x_neg ^ y_neg;
        return (~diff & (x < y)) | (x_neg & ~y_neg);
    }

    [[gnu::always_inline]]
    inline uint256_t byte(uint256_t const &byte_index_256, uint256_t const &x)
    {
        if (byte_index_256 >= 32) {
            return uint256_t{0};
        }
        uint64_t const byte_index = 31 - byte_index_256[0];
        uint64_t const word_index = byte_index >> 3;
        uint64_t const word = x[word_index];
        uint64_t const bit_index = (byte_index & 7) << 3;
        uint64_t const b = static_cast<uint8_t>(word >> bit_index);
        return uint256_t{b};
    }

    inline uint256_t
    from_bytes(std::size_t n, std::size_t remaining, uint8_t const *src)
    {
        if (n == 0) {
            return 0;
        }
        uint8_t dst[32] = {};
        std::memcpy(&dst[32 - n], src, std::min(n, remaining));
        return uint256_t::load_be(dst);
    }

    inline uint256_t from_bytes(std::size_t const n, uint8_t const *src)
    {
        return from_bytes(n, n, src);
    }

}

namespace std
{
    template <>
    struct numeric_limits<monad::vm::runtime::uint256_t>
    {
        using type = monad::vm::runtime::uint256_t;

        static constexpr bool is_specialized = true;
        static constexpr bool is_integer = true;
        static constexpr bool is_signed = false;
        static constexpr bool is_exact = true;
        static constexpr bool has_infinity = false;
        static constexpr bool has_quiet_NaN = false;
        static constexpr bool has_signaling_NaN = false;
        static constexpr float_denorm_style has_denorm = denorm_absent;
        static constexpr bool has_denorm_loss = false;
        static constexpr float_round_style round_style = round_toward_zero;
        static constexpr bool is_iec559 = false;
        static constexpr bool is_bounded = true;
        static constexpr bool is_modulo = true;
        static constexpr int digits = CHAR_BIT * sizeof(type);
        static constexpr int digits10 = int(0.3010299956639812 * digits);
        static constexpr int max_digits10 = 0;
        static constexpr int radix = 2;
        static constexpr int min_exponent = 0;
        static constexpr int min_exponent10 = 0;
        static constexpr int max_exponent = 0;
        static constexpr int max_exponent10 = 0;
        static constexpr bool traps = std::numeric_limits<unsigned>::traps;
        static constexpr bool tinyness_before = false;

        static constexpr type min() noexcept
        {
            return type{0};
        }

        static constexpr type lowest() noexcept
        {
            return min();
        }

        static constexpr type max() noexcept
        {
            return ~type{0};
        }

        static constexpr type epsilon() noexcept
        {
            return type{0};
        }

        static constexpr type round_error() noexcept
        {
            return type{0};
        }

        static constexpr type infinity() noexcept
        {
            return type{0};
        }

        static constexpr type quiet_NaN() noexcept
        {
            return type{0};
        }

        static constexpr type signaling_NaN() noexcept
        {
            return type{0};
        }

        static constexpr type denorm_min() noexcept
        {
            return type{0};
        }
    };
}

#endif
