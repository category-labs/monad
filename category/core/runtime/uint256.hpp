// Copyright (C) 2025 Category Labs, Inc.
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

#pragma once

#include <category/vm/core/assert.h>

#include <algorithm>
#include <bit>
#include <climits>
#include <cstdint>
#include <cstring>
#include <format>
#include <immintrin.h>
#include <limits>
#include <stdexcept>
#include <type_traits>

#ifndef __AVX2__
    #error "Target architecture must support AVX2"
#endif

#ifndef __BMI2__
    #error "Target architecture must support BMI2 (for MULX)"
#endif

// GCC's overeager SLP vectorizer sometimes pessimizes code. For functions that
// are particularly sensitive about this (such as multiplication), the
// vectorizer can be turned off with the MONAD_VM_NO_VECTORIZE pragma.
// Since optimization pragmas are not applied to inlined functions, any function
// that is annotated as MONAD_VM_NO_VECTORIZE should either be marked as
// noinline or only called from other MONAD_VM_NO_VECTORIZE functions.
#if defined(__GNUC__) && !defined(__clang__)
    #define MONAD_VM_NO_VECTORIZE __attribute__((optimize("no-tree-vectorize")))
#else
    #define MONAD_VM_NO_VECTORIZE
#endif

namespace monad::vm::runtime
{
    struct uint256_t;

    [[gnu::always_inline]] constexpr inline uint64_t
    force(uint64_t expr) noexcept
    {
        if !consteval {
            asm("" : "+r"(expr));
        }
        return expr;
    }

    template <typename T>
    struct result_with_carry
    {
        T value;
        bool carry;

        // Only used in unit tests
        friend inline bool operator==(
            result_with_carry const &lhs, result_with_carry const &rhs) noexcept
            requires std::equality_comparable<T>
        {
            return lhs.value == rhs.value && lhs.carry == rhs.carry;
        }
    };

    [[gnu::always_inline]]
    constexpr inline result_with_carry<uint64_t> addc_constexpr(
        uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept
    {
        uint64_t const sum = lhs + rhs;
        bool carry_out = sum < lhs;
        uint64_t const sum_carry = sum + carry_in;
        carry_out |= sum_carry < sum;
        return result_with_carry{.value = sum_carry, .carry = carry_out};
    }

    [[gnu::always_inline]]
    inline result_with_carry<uint64_t> addc_intrinsic(
        uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept
    {
        static_assert(sizeof(unsigned long long) == sizeof(uint64_t));
        unsigned long long carry_out = 0;
        uint64_t const sum_carry =
            __builtin_addcll(lhs, rhs, carry_in, &carry_out);
        return result_with_carry{
            .value = sum_carry, .carry = static_cast<bool>(carry_out)};
    }

    [[gnu::always_inline]]
    constexpr inline result_with_carry<uint64_t>
    addc(uint64_t const lhs, uint64_t const rhs, bool const carry_in) noexcept
    {
        if consteval {
            return addc_constexpr(lhs, rhs, carry_in);
        }
        else {
            return addc_intrinsic(lhs, rhs, carry_in);
        }
    }

    [[gnu::always_inline]] constexpr inline result_with_carry<uint64_t>
    subb_constexpr(
        uint64_t const lhs, uint64_t const rhs, bool const borrow_in) noexcept
    {
        uint64_t const sub = lhs - rhs;
        bool borrow_out = rhs > lhs;
        uint64_t const sub_borrow = sub - borrow_in;
        borrow_out |= borrow_in > sub;
        return result_with_carry{.value = sub_borrow, .carry = borrow_out};
    }

    [[gnu::always_inline]] inline result_with_carry<uint64_t> subb_intrinsic(
        uint64_t const lhs, uint64_t const rhs, bool const borrow_in) noexcept
    {
        static_assert(sizeof(unsigned long long) == sizeof(uint64_t));
        unsigned long long borrow_out = 0;
        uint64_t const sub_borrow =
            __builtin_subcll(lhs, rhs, borrow_in, &borrow_out);
        // If we do not force the result here, clang replaces the sub/sbb chain
        // with a long series of comparisons and flag logic which is worse
        return result_with_carry{
            .value = force(sub_borrow), .carry = static_cast<bool>(borrow_out)};
    }

    [[gnu::always_inline]] constexpr inline result_with_carry<uint64_t>
    subb(uint64_t const lhs, uint64_t const rhs, bool const borrow_in) noexcept
    {
        if consteval {
            return subb_constexpr(lhs, rhs, borrow_in);
        }
        else {
            return subb_intrinsic(lhs, rhs, borrow_in);
        }
    }

    [[gnu::always_inline]]
    inline uint64_t shld_intrinsic(
        uint64_t high, uint64_t const low, uint8_t const shift) noexcept
    {
        asm("shldq %[shift], %[low], %[high]"
            : [high] "+r"(high)
            : [low] "r"(low), [shift] "c"(shift)
            : "cc");
        return high;
    }

    [[gnu::always_inline]]
    inline constexpr uint64_t shld_constexpr(
        uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        return (high << shift) | ((low >> 1) >> (63 - shift));
    }

    [[gnu::always_inline]]
    inline constexpr uint64_t
    shld(uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        if consteval {
            return shld_constexpr(high, low, shift);
        }
        else {
            return shld_intrinsic(high, low, shift);
        }
    }

    [[gnu::always_inline]]
    inline uint64_t shrd_intrinsic(
        uint64_t const high, uint64_t low, uint8_t const shift) noexcept
    {
        asm("shrdq %[shift], %[high], %[low]"
            : [low] "+r"(low)
            : [high] "r"(high), [shift] "c"(shift)
            : "cc");
        return low;
    }

    [[gnu::always_inline]]
    inline constexpr uint64_t shrd_constexpr(
        uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        return (low >> shift) | ((high << 1) << (63 - shift));
    }

    [[gnu::always_inline]]
    inline constexpr uint64_t
    shrd(uint64_t const high, uint64_t const low, uint8_t const shift) noexcept
    {
        if consteval {
            return shrd_constexpr(high, low, shift);
        }
        else {
            return shrd_intrinsic(high, low, shift);
        }
    }

    template <typename Q, typename R = Q>
    struct div_result
    {
        Q quot;
        R rem;

        // Only used in unit tests
        friend inline bool
        operator==(div_result const &lhs, div_result const &rhs) noexcept
            requires std::equality_comparable<Q> && std::equality_comparable<R>
        {
            return lhs.quot == rhs.quot && lhs.rem == rhs.rem;
        }
    };

    typedef unsigned __int128 uint128_t;
    typedef __int128 int128_t;

    [[gnu::always_inline]]
    constexpr inline div_result<uint64_t>
    div_constexpr(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
    {
        auto const u = (static_cast<uint128_t>(u_hi) << 64) | u_lo;
        auto const quot = static_cast<uint64_t>(u / v);
        auto const rem = static_cast<uint64_t>(u % v);
        return {.quot = quot, .rem = rem};
    }

    [[gnu::always_inline]]
    inline div_result<uint64_t>
    div_intrinsic(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
    {
        asm("div %[v]" : "+d"(u_hi), "+a"(u_lo) : [v] "r"(v));
        return {.quot = u_lo, .rem = u_hi};
    }

    [[gnu::always_inline]]
    constexpr inline div_result<uint64_t>
    div(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
    {
        MONAD_VM_DEBUG_ASSERT(u_hi < v);
        if consteval {
            return div_constexpr(u_hi, u_lo, v);
        }
        else {
            return div_intrinsic(u_hi, u_lo, v);
        }
    }

    inline constexpr uint256_t byteswap(uint256_t const &x) noexcept;

    struct uint256_t
    {
        using word_type = uint64_t;
        static constexpr auto word_num_bits = sizeof(word_type) * 8;
        static constexpr auto num_bits = 256;
        static constexpr auto num_bytes = num_bits / 8;
        static constexpr auto num_words = num_bits / word_num_bits;

    private:
        std::array<uint64_t, num_words> words_{0, 0, 0, 0};

    public:
        template <typename... T>
        [[gnu::always_inline]] constexpr explicit(false)
            uint256_t(T... v) noexcept
            requires std::conjunction_v<std::is_convertible<T, uint64_t>...>
            : words_{static_cast<uint64_t>(v)...}
        {
        }

        template <typename T>
        [[gnu::always_inline]] constexpr explicit(false)
            uint256_t(T x0) noexcept
            requires std::is_convertible_v<T, uint64_t>
            : words_{static_cast<uint64_t>(x0), 0, 0, 0}
        {
            // GCC produces better code for words_{x0, 0, 0, 0} than for
            // words_{x0}
        }

        [[gnu::always_inline]] constexpr explicit(true)
            uint256_t(std::array<uint64_t, 4> const &x) noexcept
            : words_{x}
        {
        }

        [[gnu::always_inline]]
        explicit(true) uint256_t(__m256i x) noexcept
        {
            // Clang sometimes miscompiles the std::bit_cast equivalent into a
            // much slower version, so we prefer memcpy here
            std::memcpy(&words_, &x, sizeof(words_));
        }

        [[gnu::always_inline]]
        inline __m256i to_avx() const noexcept
        {
            __m256i result;
            std::memcpy(&result, &words_, sizeof(result));
            return result;
        }

        [[gnu::always_inline]]
        inline constexpr explicit operator bool() const noexcept
        {
            auto const w0 = force(words_[0]);
            auto const w1 = force(words_[1]);
            auto const w2 = force(words_[2]);
            auto const w3 = force(words_[3]);
            return force(w0 | w1) | force(w2 | w3);
        }

        template <typename Int>
        [[gnu::always_inline]]
        inline constexpr explicit operator Int() const noexcept
            requires(
                std::is_integral_v<Int> && sizeof(Int) <= sizeof(word_type))
        {
            return static_cast<Int>(words_[0]);
        }

        [[gnu::always_inline]]
        inline constexpr uint64_t &operator[](size_t i) noexcept
        {
            return words_[i];
        }

        [[gnu::always_inline]]
        inline constexpr uint64_t const &operator[](size_t i) const noexcept
        {
            return words_[i];
        }

        [[gnu::always_inline]]
        inline uint8_t *as_bytes() noexcept
        {
            return reinterpret_cast<uint8_t *>(&words_);
        }

        [[gnu::always_inline]]
        inline uint8_t const *as_bytes() const noexcept
        {
            return reinterpret_cast<uint8_t const *>(&words_);
        }

        [[gnu::always_inline]]
        inline constexpr std::array<uint64_t, 4> &as_words() noexcept
        {
            return words_;
        }

        [[gnu::always_inline]]
        inline constexpr std::array<uint64_t, 4> const &
        as_words() const noexcept
        {
            return words_;
        }

        friend inline constexpr uint256_t
        operator/(uint256_t const &x, uint256_t const &y) noexcept;

        friend inline constexpr uint256_t
        operator%(uint256_t const &x, uint256_t const &y) noexcept;

        [[gnu::always_inline]]
        friend inline constexpr result_with_carry<uint256_t>
        subb(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            auto [w0, b0] = subb(lhs[0], rhs[0], false);
            auto [w1, b1] = subb(lhs[1], rhs[1], b0);
            auto [w2, b2] = subb(lhs[2], rhs[2], b1);
            auto [w3, b3] = subb(lhs[3], rhs[3], b2);
            return {.value = uint256_t{w0, w1, w2, w3}, .carry = b3};
        }

        [[gnu::always_inline]]
        friend inline constexpr result_with_carry<uint256_t>
        addc(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            auto [w0, c0] = addc(lhs[0], rhs[0], false);
            auto [w1, c1] = addc(lhs[1], rhs[1], c0);
            auto [w2, c2] = addc(lhs[2], rhs[2], c1);
            auto [w3, c3] = addc(lhs[3], rhs[3], c2);
            return {.value = uint256_t{w0, w1, w2, w3}, .carry = c3};
        }

        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        operator+(uint256_t const &lhs, uint256_t const &rhs) noexcept

        {
            return addc(lhs, rhs).value;
        }

        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        operator-(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            return subb(lhs, rhs).value;
        }

        [[gnu::always_inline]]
        friend inline constexpr bool
        operator<(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            return subb(lhs, rhs).carry;
        }

        [[gnu::always_inline]]
        friend inline constexpr bool
        operator<=(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            return !(lhs > rhs);
        }

        [[gnu::always_inline]]
        friend inline constexpr bool
        operator>(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            return rhs < lhs;
        }

        [[gnu::always_inline]]
        friend inline constexpr bool
        operator>=(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            return !(lhs < rhs);
        }

        // NOLINTBEGIN(bugprone-macro-parentheses)

#define BITWISE_BINOP(return_ty, op_name)                                      \
    [[gnu::always_inline]] friend inline constexpr return_ty operator op_name( \
        uint256_t const &x, uint256_t const &y) noexcept                       \
    {                                                                          \
        return uint256_t{                                                      \
            x[0] op_name y[0],                                                 \
            x[1] op_name y[1],                                                 \
            x[2] op_name y[2],                                                 \
            x[3] op_name y[3]};                                                \
    }
        BITWISE_BINOP(uint256_t, &);
        BITWISE_BINOP(uint256_t, |);
        BITWISE_BINOP(uint256_t, ^);
#undef BITWISE_BINOP

        // NOLINTEND(bugprone-macro-parentheses)

        [[gnu::always_inline]] friend inline constexpr bool
        operator==(uint256_t const &x, uint256_t const &y) noexcept
        {
            auto const e0 = force(x[0] ^ y[0]);
            auto const e1 = force(x[1] ^ y[1]);
            auto const e2 = force(x[2] ^ y[2]);
            auto const e3 = force(x[3] ^ y[3]);
            return !(force(e0 | e1) | force(e2 | e3));
        }

        [[gnu::always_inline]] inline constexpr uint256_t
        operator-() const noexcept
        {
            return 0 - *this;
        }

        [[gnu::always_inline]] inline constexpr uint256_t
        operator~() const noexcept
        {
            return uint256_t{~words_[0], ~words_[1], ~words_[2], ~words_[3]};
        }

        template <typename T>
        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        operator<<(uint256_t const &x, T shift0) noexcept
            requires std::is_convertible_v<T, uint64_t>
        {
            if (MONAD_VM_UNLIKELY(static_cast<uint64_t>(shift0) >= 256)) {
                return 0;
            }
            auto shift = static_cast<uint8_t>(shift0);
            if (shift < 128) {
                if (shift < 64) {
                    return uint256_t{
                        x[0] << shift,
                        shld(x[1], x[0], shift),
                        shld(x[2], x[1], shift),
                        shld(x[3], x[2], shift),
                    };
                }
                else {
                    shift &= 63;
                    return uint256_t{
                        0,
                        x[0] << shift,
                        shld(x[1], x[0], shift),
                        shld(x[2], x[1], shift),
                    };
                }
            }
            else {
                if (shift < 192) {
                    shift &= 127;
                    return uint256_t{
                        0,
                        0,
                        x[0] << shift,
                        shld(x[1], x[0], shift),
                    };
                }
                else {
                    shift &= 63;
                    return uint256_t{0, 0, 0, x[0] << shift};
                }
            }
        }

        [[gnu::always_inline]]
        inline constexpr uint256_t &
        operator<<=(uint256_t const &shift0) noexcept
        {
            return *this = *this << shift0;
        }

        [[gnu::always_inline]] friend inline constexpr uint256_t
        operator<<(uint256_t const &x, uint256_t const &shift) noexcept
        {
            if (MONAD_VM_UNLIKELY(shift[3] | shift[2] | shift[1])) {
                return 0;
            }
            return x << shift[0];
        }

        enum class RightShiftType
        {
            Arithmetic,
            Logical
        };

        template <RightShiftType type>
        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        shift_right(uint256_t const &x, uint256_t shift0) noexcept
        {
            uint64_t fill;
            if constexpr (type == RightShiftType::Logical) {
                fill = 0;
            }
            else {
                int64_t const sign_bit = static_cast<int64_t>(x[3]) &
                                         std::numeric_limits<int64_t>::min();
                fill = static_cast<uint64_t>(sign_bit >> 63);
            }
            if (MONAD_VM_UNLIKELY(
                    shift0[3] | shift0[2] | shift0[1] | (shift0[0] >= 256))) {
                return uint256_t{fill, fill, fill, fill};
            }
            auto shift = static_cast<uint8_t>(shift0);
            uint64_t tail;
            if constexpr (type == RightShiftType::Logical) {
                tail = x[3] >> (shift & 63);
            }
            else {
                tail = shrd(fill, x[3], shift & 63);
            }
            if (shift < 128) {
                if (shift < 64) {
                    return uint256_t{
                        shrd(x[1], x[0], shift),
                        shrd(x[2], x[1], shift),
                        shrd(x[3], x[2], shift),
                        tail,
                    };
                }
                else {
                    shift &= 63;
                    return uint256_t{
                        shrd(x[2], x[1], shift),
                        shrd(x[3], x[2], shift),
                        tail,
                        fill};
                }
            }
            else {
                if (shift < 192) {
                    shift &= 127;
                    return uint256_t{shrd(x[3], x[2], shift), tail, fill, fill};
                }
                else {
                    shift &= 63;
                    return uint256_t{tail, fill, fill, fill};
                }
            }
        }

        [[gnu::always_inline]] friend inline constexpr uint256_t
        operator>>(uint256_t const &x, uint256_t const &shift) noexcept
        {
            return shift_right<RightShiftType::Logical>(x, shift);
        }

        [[gnu::always_inline]]
        inline constexpr uint256_t &operator>>=(uint256_t const &shift) noexcept
        {
            return *this = *this >> shift;
        }

        [[gnu::always_inline]]
        inline constexpr uint256_t to_be() const noexcept
        {
            static_assert(
                std::endian::native == std::endian::little,
                "to_be only supported on little-endian platforms");
            return byteswap(*this);
        }

        [[gnu::always_inline]]
        static inline constexpr uint256_t
        load_be(uint8_t const (&bytes)[num_bytes]) noexcept
        {
            return load_le(bytes).to_be();
        }

        [[gnu::always_inline]]
        static inline constexpr uint256_t
        load_le(uint8_t const (&bytes)[num_bytes]) noexcept
        {
            return load_le_unsafe(bytes);
        }

        [[gnu::always_inline]]
        static inline constexpr uint256_t
        load_be_unsafe(uint8_t const *bytes) noexcept
        {
            return load_le_unsafe(bytes).to_be();
        }

        [[gnu::always_inline]] static inline constexpr uint256_t
        load_le_unsafe(uint8_t const *bytes) noexcept
        {
            static_assert(std::endian::native == std::endian::little);
            uint256_t result;
            std::memcpy(&result.words_, bytes, num_bytes);
            return result;
        }

        template <typename DstT>
        [[gnu::always_inline]]
        inline DstT store_be() const noexcept
        {
            DstT result;
            static_assert(sizeof(result.bytes) == sizeof(words_));
            store_be(result.bytes);
            return result;
        }

        [[gnu::always_inline]]
        inline void store_be(uint8_t *dest) const noexcept
        {
            uint256_t const be = to_be();
            std::memcpy(dest, &be.words_, num_bytes);
        }

        [[gnu::always_inline]]
        inline void store_le(uint8_t *dest) const noexcept
        {
            std::memcpy(dest, &words_, num_bytes);
        }

        // String conversion functions
        // These are not optimized and should never be used in
        // performance-critical code.
        inline std::string to_string(int const base0) const;
        static inline constexpr uint256_t from_string(char const *s);

        [[gnu::always_inline]] static inline constexpr uint256_t
        from_string(std::string const &s)
        {
            return from_string(s.c_str());
        }
    };

    static_assert(std::is_trivially_copyable_v<uint256_t>);

    uint256_t signextend(uint256_t const &byte_index, uint256_t const &x);

    [[gnu::always_inline]]
    inline uint256_t sar(uint256_t const &shift, uint256_t const &x)
    {
        return shift_right<uint256_t::RightShiftType::Arithmetic>(x, shift);
    }

    uint256_t countr_zero(uint256_t const &x);

    constexpr size_t popcount(uint256_t const &x)
    {
        return static_cast<size_t>(std::popcount(x[0])) +
               static_cast<size_t>(std::popcount(x[1])) +
               static_cast<size_t>(std::popcount(x[2])) +
               static_cast<size_t>(std::popcount(x[3]));
    }

    template <size_t N>
    [[gnu::always_inline]] inline constexpr uint32_t
    count_significant_words(std::array<uint64_t, N> const &x) noexcept
    {
        for (size_t i = N; i > 0; --i) {
            if (x[i - 1] != 0) {
                return static_cast<uint32_t>(i);
            }
        }
        return 0;
    }

    [[gnu::always_inline]]
    inline constexpr uint32_t
    count_significant_bytes(uint256_t const &x) noexcept
    {
        auto const significant_words = count_significant_words(x.as_words());
        if (significant_words == 0) {
            return 0;
        }
        else {
            auto const leading_word = x[significant_words - 1];
            auto const leading_significant_bytes = static_cast<uint32_t>(
                (64 - std::countl_zero(leading_word) + 7) / 8);
            return leading_significant_bytes + (significant_words - 1) * 8;
        }
    }

    [[gnu::always_inline]]
    inline constexpr void mulx_constexpr(
        uint64_t const x, uint64_t const y, uint64_t &r_hi,
        uint64_t &r_lo) noexcept
    {
        uint128_t const prod =
            static_cast<uint128_t>(x) * static_cast<uint128_t>(y);
        r_hi = static_cast<uint64_t>(prod >> uint128_t{64});
        r_lo = static_cast<uint64_t>(prod);
    }

    [[gnu::always_inline]]
    inline void mulx_intrinsic(
        uint64_t const x, uint64_t const y, uint64_t &r_hi,
        uint64_t &r_lo) noexcept
    {
        /*
        uint64_t hi;
        uint64_t lo;
        */
        asm("mulx %[x], %[lo], %[hi]"
            : [hi] "=r"(r_hi), [lo] "=r"(r_lo)
            : [x] "r"(x), [y] "d"(y));
    }

    [[gnu::always_inline]]
    inline constexpr void mulx(
        uint64_t const x, uint64_t const y, uint64_t &r_hi,
        uint64_t &r_lo) noexcept
    {
        if consteval {
            return mulx_constexpr(x, y, r_hi, r_lo);
        }
        else {
            return mulx_intrinsic(x, y, r_hi, r_lo);
        }
    }

    template <size_t M>
    using words_t = std::array<uint64_t, M>;

    [[gnu::always_inline]]
    inline void adc_3(
        uint64_t x_2, uint64_t x_1, uint64_t x_0, uint64_t const y_1,
        uint64_t const y_0, uint64_t &r_2, uint64_t &r_1,
        uint64_t &r_0) noexcept
    {
        asm("addq %[y_0], %[x_0]\n"
            "adcq %[y_1], %[x_1]\n"
            "adcq $0, %[x_2]"
            : [x_0] "+r"(x_0), [x_1] "+r"(x_1), [x_2] "+r"(x_2)
            : [y_0] "r"(y_0), [y_1] "r"(y_1)
            : "cc");
        r_2 = x_2;
        r_1 = x_1;
        r_0 = x_0;
    }

    [[gnu::always_inline]]
    inline void adc_2(
        uint64_t x_1, uint64_t x_0, uint64_t const y_0, uint64_t &r_1,
        uint64_t &r_0) noexcept
    {
        asm("addq %[y_0], %[x_0]\n"
            "adcq $0, %[x_1]"
            : [x_0] "+r"(x_0), [x_1] "+r"(x_1)
            : [y_0] "r"(y_0)
            : "cc");
        r_1 = x_1;
        r_0 = x_0;
    }

    [[gnu::always_inline]]
    inline void adc_2(
        uint64_t x_1, uint64_t x_0, uint64_t const y_1, uint64_t const y_0,
        uint64_t &r_1, uint64_t &r_0) noexcept
    {
        asm("addq %[y_0], %[x_0]\n"
            "adcq %[y_1], %[x_1]"
            : [x_0] "+r"(x_0), [x_1] "+r"(x_1)
            : [y_0] "r"(y_0), [y_1] "r"(y_1)
            : "cc");
        r_1 = x_1;
        r_0 = x_0;
    }

    template <size_t I, size_t R, size_t M>
    [[gnu::always_inline]]
    inline void mul_line_recur(
        words_t<M> const &x, uint64_t const y, words_t<R> &__restrict__ result,
        uint64_t carry) noexcept
    {
        if constexpr (I < std::min(R, M)) {
            if constexpr (I + 1 < R) {
                uint64_t hi;
                uint64_t lo;
                mulx(x[I], y, hi, lo);
                adc_2(
                    // Input 1
                    hi,
                    lo,
                    // Input 2
                    carry,
                    // Output
                    carry,
                    result[I]);
                mul_line_recur<I + 1, R, M>(x, y, result, carry);
            }
            else {
                result[I] = y * x[I] + carry;
            }
        }
        else if constexpr (M < R) {
            result[M] = carry;
        }
    }

    // result[0 .. min(M + 1, R)) = y * x[0 .. M)
    template <size_t R, size_t M>
    [[gnu::always_inline]]
    inline void mul_line(
        words_t<M> const &x, uint64_t const y,
        words_t<R> &__restrict__ result) noexcept
    {
        uint64_t carry;
        mulx(y, x[0], carry, result[0]);

        mul_line_recur<1, R, M>(x, y, result, carry);
    }

    template <size_t J, size_t I, size_t R, size_t M>
    [[gnu::always_inline]]
    inline void mul_add_line_recur(
        words_t<M> const &x, uint64_t const y_i,
        words_t<R> &__restrict__ result, uint64_t c_hi, uint64_t c_lo) noexcept
    {
        if constexpr (J + 1 < M && I + J < R) {
            if constexpr (I + J + 2 < R) {
                // We need c_lo, c_hi
                uint64_t hi;
                uint64_t lo;
                mulx(x[J + 1], y_i, hi, lo);
                adc_3(
                    // Input 1
                    hi,
                    lo,
                    result[I + J],
                    // Input 2
                    c_hi,
                    c_lo,
                    // Result
                    c_hi,
                    c_lo,
                    result[I + J]);
            }
            else if constexpr (I + J + 1 < R) {
                // We only need c_lo
                uint64_t const lo = x[J + 1] * y_i;
                adc_2(
                    // Input 1
                    lo,
                    result[I + J],
                    // Input 2
                    c_hi,
                    c_lo,
                    // Output
                    c_lo,
                    result[I + J]);
            }
            else {
                // We're done, we don't need subsequent results
                result[I + J] += c_lo;
            }
            mul_add_line_recur<J + 1, I, R, M>(x, y_i, result, c_hi, c_lo);
        }
        else {
            if constexpr (I + M < R) {

                adc_2(
                    // Input 1
                    c_hi,
                    c_lo,
                    // Input 2
                    result[I + M - 1],
                    // Output
                    result[I + M],
                    result[I + M - 1]);
            }
            else if constexpr (I + M < R + 1) {
                result[I + M - 1] += c_lo;
            }
        }
    }

    // result[i .. min(i + M + 1, R)) += y_i * x[0 .. M)
    template <size_t I, size_t R, size_t M>
    [[gnu::always_inline]]
    inline void mul_add_line(
        words_t<M> const &x, uint64_t const y_i,
        words_t<R> &__restrict__ result) noexcept
    {
        // A naive implementation would use a single carry variable. However
        // this means on every iteration we compute
        //     result[i+j] = result[i+j] + prod_lo + carry
        // which needs to propagate two carry bits. This causes a slew of
        // setb/xor/movxz instructions to be inserted.
        // Instead, we widen the carry and skew the loop so that every iteration
        // computes
        //     result[i+j] = result[i+j] + c_lo
        //     c_lo = prod_lo + c_hi (+ carry)
        //     c_hi = prod_hi (+ carry)
        uint64_t c_hi;
        uint64_t c_lo;

        if constexpr (I + 1 < R) {
            mulx(x[0], y_i, c_hi, c_lo);
        }
        else {
            c_hi = 0;
            c_lo = x[0] * y_i;
        }
        mul_add_line_recur<0, I, R, M>(x, y_i, result, c_hi, c_lo);
    }

    template <size_t I, size_t R, size_t M, size_t N>
    [[gnu::always_inline]]
    inline void truncating_mul_runtime_recur(
        words_t<M> const &x, words_t<N> const &y,
        words_t<R> &__restrict__ result) noexcept
    {
        if constexpr (I < N) {
            mul_add_line<I, R, M>(x, y[I], result);
            truncating_mul_runtime_recur<I + 1, R, M>(x, y, result);
        }
    }

    template <size_t R, size_t M, size_t N>
    [[gnu::always_inline]]
    inline words_t<R>
    truncating_mul_runtime(words_t<M> const &x, words_t<N> const &y) noexcept
        requires(0 < R && 0 < M && 0 < N && R <= M + N)
    {
        words_t<R> result;
        mul_line<R>(x, y[0], result);
        truncating_mul_runtime_recur<1, R, M, N>(x, y, result);
        return result;
    }

    template <size_t R, size_t M, size_t N>
    [[gnu::always_inline]]
    inline constexpr words_t<R>
    truncating_mul_constexpr(words_t<M> const &x, words_t<N> const &y) noexcept
        requires(0 < R && R <= M + N)
    {
        words_t<R> result{0};
        for (size_t j = 0; j < N; j++) {
            uint64_t carry = 0;
            for (size_t i = 0; i < M && i + j < R; i++) {
                uint64_t hi;
                uint64_t lo;
                mulx(x[i], y[j], hi, lo);

                auto const [s0, c0] = addc(lo, result[i + j], false);
                auto const [s1, c1] = addc(s0, carry, false);
                result[i + j] = s1;
                auto const [s2, c2] = addc(hi, c0, c1);
                carry = s2;
            }
            if (j + M < R) {
                result[j + M] = carry;
            }
        }
        return result;
    }

    /**
     * Truncating multi-word multiplication. Multiply a M-word number by a
     * N-word number, discarding the M+N-R higher words. When R = M+N, this
     * corresponds to full precision multiplication
     */
    template <size_t R, size_t M, size_t N>
    MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
    inline constexpr words_t<R>
    truncating_mul(words_t<M> const &x, words_t<N> const &y) noexcept
        requires(0 < R && 0 < M && 0 < N && R <= M + N)
    {
        if consteval {
            return truncating_mul_constexpr<R, M, N>(x, y);
        }
        else {
            return truncating_mul_runtime<R, M, N>(x, y);
        }
    }

    MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
    inline constexpr uint256_t
    truncating_mul(uint256_t const &x, uint256_t const &y) noexcept
    {
        return uint256_t{
            truncating_mul<uint256_t::num_words>(x.as_words(), y.as_words())};
    }

    MONAD_VM_NO_VECTORIZE
    [[gnu::noinline]]
    inline constexpr uint256_t
    operator*(uint256_t const &lhs, uint256_t const &rhs) noexcept
    {
        return truncating_mul(lhs, rhs);
    }

    [[gnu::always_inline]]
    constexpr uint64_t
    long_div(size_t m, uint64_t const *u, uint64_t v, uint64_t *quot)
    {
        MONAD_VM_DEBUG_ASSERT(m);
        MONAD_VM_DEBUG_ASSERT(v);
        auto r = div(0, u[m - 1], v);
        quot[m - 1] = r.quot;
        for (int i = static_cast<int>(m - 2); i >= 0; i--) {
            auto const ix = static_cast<size_t>(i);
            r = div(r.rem, u[ix], v);
            quot[ix] = r.quot;
        }
        return r.rem;
    }

    constexpr void knuth_div(
        size_t m, uint64_t *u, size_t n, uint64_t const *v, uint64_t *quot)
    {
        constexpr size_t BASE_SHIFT = 64;

        MONAD_VM_DEBUG_ASSERT(m >= n);
        MONAD_VM_DEBUG_ASSERT(n > 1);
        MONAD_VM_DEBUG_ASSERT(v[n - 1] & (uint64_t{1} << 63));

        for (int i = static_cast<int>(m - n); i >= 0; i--) {
            auto const ix = static_cast<size_t>(i);
            uint128_t q_hat;
            // We diverge from the algorithms in Knuth AOCP and Hacker's Delight
            // as we need to check for potential division overflow before
            // dividing.

            // u[ix + n] > v[n-1] is never the case:
            // 1. In the first iteration, u[ix + n] is always the extra
            // numerator word used to fit the normalization shift and therefore
            // it is either 0 (if shift = 0) or strictly less than v[n-1]
            // 2. In subsequent iterations, (u[ix+n .. ix]) is the
            // remainder of division by (v[n-1 .. 0]), whence u[ix+n] <= v[n-1]
            MONAD_VM_DEBUG_ASSERT(u[ix + n] <= v[n - 1]);
            if (MONAD_VM_UNLIKELY(u[ix + n] == v[n - 1])) {
                q_hat = ~uint64_t{0};

                // In this branch, we have q_hat-1 <= q <= q_hat, therefore only
                // one adjustment of the quotient is necessary, so we skip the
                // pre-adjustment phase.
                //
                // Suppose q >= q_hat-2, and let term = BASE*u[ix+n] + u[ix+n-1]
                //   r_hat = term - q_hat*v[n-1]
                //        >= term - (q-2)*v[n-1]
                //         = term - q*v[n-1] + 2*v[n-1]
                //        >= 2 * v[n-1]
                //        >= BASE
                // The last inequality follows from v[n-1] > BASE/2 and
                // term - q*v[n-1] >= 0 follows from u[ix + n] = v[n - 1],
                // because
                //   BASE*u[ix+n] + u[ix+n-1] - q*v[n-1]
                //     = BASE*v[n-1] + u[ix+n-1] - q*v[n-1]
                //    >= BASE*v[n-1] - q*v[n-1]
                //    >= BASE*v[n-1] - BASE*v[n-1]
                //     = 0
                // However, if r_hat >= BASE, then q_hat <= q. To this end
                // it suffices to prove
                //   u[ix+n .. ix] - v[n-1, .., 0] * q_hat >= 0
                // because q <= q_hat
                // and u[ix+n .. ix] - v[n-1, .., 0] * q >= 0,
                //   u[ix+n .. ix] - v[n-1 .. 0]*q_hat
                //     = (u[ix+n .. ix+n-1] - v[n-1]*q_hat)*B^(n-1)
                //       + u[ix+n-2 .. ix] - v[n-2 .. 0]*q_hat
                //     = r_hat*B^(n-1) + u[ix+n-2 .. ix] - v[n-2 .. 0]*q_hat
                //    >= B^n + u[ix+n-2 .. ix] - v[n-2 .. 0] * q_hat
                //    >= B^n - v[n-2 .. 0] * q_hat
                //    >= B^n - B^(n-1) * B
                //     = 0
                // Therefore if q >= q_hat-2 we have q <= q_hat which is a
                // contradiction.
            }
            else {
                auto [q_hat0, r_hat0] = div(u[ix + n], u[ix + n - 1], v[n - 1]);
                if (q_hat0 == 0) {
                    continue;
                }

                q_hat = q_hat0;
                uint128_t const r_hat = r_hat0;

                if (q_hat * v[n - 2] > (r_hat << BASE_SHIFT) + u[ix + n - 2]) {
                    q_hat--;
                }
            }

            // u[ix+n .. ix] -= q_hat * v[n .. 0]
            uint128_t t = 0;
            uint128_t k = 0;
            for (size_t j = 0; j < n; j++) {
                uint128_t const prod = q_hat * v[j];
                t = u[j + ix] - k - (prod & 0xffffffffffffffff);
                u[j + ix] = static_cast<uint64_t>(t);
                k = (prod >> 64) -
                    static_cast<uint128_t>(static_cast<int128_t>(t) >> 64);
            }
            t = u[ix + n] - k;
            u[ix + n] = static_cast<uint64_t>(t);

            // Our estimate for q_hat was one too high
            // u[ix+n .. ix] += v[n .. 0]
            // q_hat -= 1
            if (t >> 127) {
                q_hat -= 1;
                uint128_t k = 0;
                for (size_t j = 0; j < n; j++) {
                    t = static_cast<uint128_t>(u[ix + j]) + v[j] + k;
                    u[ix + j] = static_cast<uint64_t>(t);
                    k = t >> 64;
                }
                u[ix + n] += static_cast<uint64_t>(k);
            }
            quot[ix] = static_cast<uint64_t>(q_hat);
        }
    }

    template <size_t M, size_t N>
    inline constexpr div_result<words_t<M>, words_t<N>>
    udivrem(words_t<M> const &u, words_t<N> const &v) noexcept
    {
        auto const m = count_significant_words(u);
        auto const n = count_significant_words(v);

        // Check division by 0
        MONAD_VM_ASSERT(n);
        if (m < n) {
            div_result<words_t<M>, words_t<N>> result;
            result.quot = {0};
            if consteval {
                for (size_t i = 0; i < N; i++) {
                    result.rem[i] = u[i];
                }
            }
            else {
                std::memcpy(&result.rem, &u, sizeof(result.rem));
            }
            return result;
        }

        if (m == 1) {
            // 1 = m >= n > 0 therefore n = 1
            auto [q0, r0] = div(0, u[0], v[0]);
            return {.quot = {q0}, .rem = {r0}};
        }

        div_result<words_t<M>, words_t<N>> result{.quot = {0}, .rem = {0}};
        if (n == 1) {
            result.rem[0] = long_div(m, &u[0], v[0], &result.quot[0]);
            return result;
        }

        auto const normalize_shift =
            static_cast<uint8_t>(std::countl_zero(v[n - 1]));

        // Extra word so the normalization shift never overflows u
        words_t<M + 1> u_norm;
        u_norm[0] = u[0] << normalize_shift;
        for (size_t i = 1; i < M; i++) {
            u_norm[i] = shld(u[i], u[i - 1], normalize_shift);
        }
        u_norm[M] = u[M - 1] >> 1 >> (63 - normalize_shift);

        words_t<N> v_norm;
        v_norm[0] = v[0] << normalize_shift;
        for (size_t i = 1; i < N; i++) {
            v_norm[i] = shld(v[i], v[i - 1], normalize_shift);
        }

        knuth_div(m, &u_norm[0], n, &v_norm[0], &result.quot[0]);

        for (size_t i = 0; i < N - 1; i++) {
            result.rem[i] = shrd(u_norm[i + 1], u_norm[i], normalize_shift);
        }
        result.rem[N - 1] = u_norm[N - 1] >> normalize_shift;

        return result;
    }

    [[gnu::always_inline]] constexpr inline div_result<uint256_t>
    udivrem(uint256_t const &u, uint256_t const &v) noexcept
    {
        auto const r = udivrem(u.as_words(), v.as_words());
        return {.quot = uint256_t{r.quot}, .rem = uint256_t{r.rem}};
    }

    inline constexpr uint256_t addmod(
        uint256_t const &x, uint256_t const &y, uint256_t const &mod) noexcept
    {
        // Fast path when mod >= 2^192 and x, y < 2*mod
        if (mod[3] && (x[3] <= mod[3]) && (y[3] <= mod[3])) {
            // x, y < 2 * mod
            auto const [x_sub, x_borrow] = subb(x, mod);
            uint256_t const x_norm = x_borrow ? x : x_sub;

            auto const [y_sub, y_borrow] = subb(y, mod);
            uint256_t const y_norm = y_borrow ? y : y_sub;

            // x_norm, y_norm < mod
            auto const [xy_sum, xy_carry] = addc(x_norm, y_norm);

            // xy_sum + (xy_carry<<256) < 2 * mod
            auto const [rem, rem_borrow] = subb(xy_sum, mod);
            if (xy_carry || !rem_borrow) {
                // xy_sum + (xy_carry<<256) >= mod
                return rem;
            }
            else {
                return xy_sum;
            }
        }
        words_t<uint256_t::num_words + 1> sum;
        uint64_t carry = 0;
#pragma GCC unroll(4)
        for (size_t i = 0; i < uint256_t::num_words; i++) {
            auto const [si, ci] = addc(x[i], y[i], carry);
            sum[i] = si;
            carry = ci;
        }
        sum[uint256_t::num_words] = carry;

        return uint256_t{udivrem(sum, mod.as_words()).rem};
    }

    MONAD_VM_NO_VECTORIZE
    [[gnu::noinline]]
    inline constexpr uint256_t mulmod(
        uint256_t const &u, uint256_t const &v, uint256_t const &mod) noexcept
    {
        auto const prod = truncating_mul<2 * uint256_t::num_words>(
            u.as_words(), v.as_words());
        return uint256_t{udivrem(prod, mod.as_words()).rem};
    }

    [[gnu::always_inline]] inline constexpr uint256_t
    operator/(uint256_t const &x, uint256_t const &y) noexcept
    {
        return udivrem(x, y).quot;
    }

    [[gnu::always_inline]] inline constexpr uint256_t
    operator%(uint256_t const &x, uint256_t const &y) noexcept
    {
        return udivrem(x, y).rem;
    }

    [[gnu::always_inline]]
    inline constexpr div_result<uint256_t>
    sdivrem(uint256_t const &x, uint256_t const &y) noexcept
    {
        auto const sign_bit = uint64_t{1} << 63;
        auto const x_neg = x[uint256_t::num_words - 1] & sign_bit;
        auto const y_neg = y[uint256_t::num_words - 1] & sign_bit;

        auto const x_abs = x_neg ? -x : x;
        auto const y_abs = y_neg ? -y : y;

        auto const quot_neg = x_neg ^ y_neg;

        auto const result = udivrem(x_abs, y_abs);

        return {
            uint256_t{quot_neg ? -result.quot : result.quot},
            uint256_t{x_neg ? -result.rem : result.rem}};
    }

    [[gnu::always_inline]]
    inline constexpr bool slt(uint256_t const &x, uint256_t const &y) noexcept
    {
        auto const x_neg = x[uint256_t::num_words - 1] >> 63;
        auto const y_neg = y[uint256_t::num_words - 1] >> 63;
        auto const diff = x_neg ^ y_neg;
        // intx branches on the sign bit, which will be mispredicted on
        // random data ~50% of the time. The branchless version does not add
        // much overhead so it is probably worth it
        return (~diff & (x < y)) | (x_neg & ~y_neg);
    }

    MONAD_VM_NO_VECTORIZE
    [[gnu::noinline]] inline constexpr uint256_t
    exp(uint256_t base, uint256_t const &exponent) noexcept
    {
        uint256_t result{1};
        if (base == 2) {
            return result << exponent;
        }

        size_t const sig_words = count_significant_words(exponent.as_words());
        for (size_t w = 0; w < sig_words; w++) {
            uint64_t word_exp = exponent[w];
            int32_t significant_bits =
                w + 1 == sig_words ? 64 - std::countl_zero(word_exp) : 64;
            while (significant_bits) {
                if (word_exp & 1) {
                    result = truncating_mul(result, base);
                }
                base = truncating_mul(base, base);
                word_exp >>= 1;
                significant_bits -= 1;
            }
        }
        return result;
    }

    [[gnu::always_inline]]
    inline uint256_t byte(uint256_t const &byte_index_256, uint256_t const &x)
    {
        if (byte_index_256 >= 32) {
            return 0;
        }
        uint64_t const byte_index = 31 - byte_index_256[0];
        uint64_t const word_index = byte_index >> 3;
        uint64_t const word = x[word_index];
        uint64_t const bit_index = (byte_index & 7) * 8;
        uint64_t const byte = static_cast<uint8_t>(word >> bit_index);
        uint256_t ret{0};
        ret[0] = byte;
        return ret;
    }

    [[gnu::always_inline]] inline constexpr uint256_t
    byteswap(uint256_t const &x) noexcept
    {
        return uint256_t{
            std::byteswap(x[3]),
            std::byteswap(x[2]),
            std::byteswap(x[1]),
            std::byteswap(x[0])};
    }

    consteval uint256_t operator""_u256(char const *s)
    {
        return uint256_t::from_string(s);
    }

    /**
     * Parse a range of raw bytes with length `n` into a 256-bit big-endian
     * word value.
     *
     * If there are fewer than `n` bytes remaining in the source data (that
     * is, `remaining < n`), then treat the input as if it had been padded
     * to the right with zero bytes.
     */
    uint256_t
    from_bytes(std::size_t n, std::size_t remaining, uint8_t const *src);

    /**
     * Parse a range of raw bytes with length `n` into a 256-bit big-endian
     * word value.
     *
     * There must be at least `n` bytes readable from `src`; if there are
     * not, use the safe overload that allows for the number of bytes
     * remaining to be specified.
     */
    uint256_t from_bytes(std::size_t n, uint8_t const *src);

    inline constexpr size_t countl_zero(uint256_t const &x)
    {
        size_t cnt = 0;
        for (size_t i = 0; i < uint256_t::num_words; i++) {
            cnt += static_cast<size_t>(std::countl_zero(x[3 - i]));
            if (cnt != ((i + 1U) * 64U)) {
                return cnt;
            }
        }
        return cnt;
    }

    consteval uint256_t pow2(size_t n)
    {
        return uint256_t{1} << n;
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
            return 0;
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
            return 0;
        }

        static constexpr type round_error() noexcept
        {
            return 0;
        }

        static constexpr type infinity() noexcept
        {
            return 0;
        }

        static constexpr type quiet_NaN() noexcept
        {
            return 0;
        }

        static constexpr type signaling_NaN() noexcept
        {
            return 0;
        }

        static constexpr type denorm_min() noexcept
        {
            return 0;
        }
    };
}

namespace monad::vm::runtime
{
    inline size_t bit_width(uint256_t const &x)
    {
        return static_cast<size_t>(std::numeric_limits<uint256_t>::digits) -
               countl_zero(x);
    }

    [[gnu::always_inline]]
    inline constexpr uint8_t from_dec(char const chr)
    {
        if (chr >= '0' && chr <= '9') {
            return static_cast<uint8_t>(chr - '0');
        }
        throw std::invalid_argument("invalid digit");
    }

    [[gnu::always_inline]]
    inline constexpr uint8_t from_hex(char const chr)
    {
        char const chr_lower = static_cast<char>(chr | 0b00100000);
        if (chr_lower >= 'a' && chr_lower <= 'f') {
            return static_cast<uint8_t>(chr_lower - 'a' + 10);
        }
        return from_dec(chr);
    }

    inline std::string uint256_t::to_string(int const base0 = 10) const
    {
        MONAD_VM_ASSERT(base0 >= 2 && base0 <= 36);

        auto num = *this;
        auto const base = uint256_t{base0};

        std::string buffer{};
        do {
            auto const [div, rem] = udivrem(num, base);
            auto const lsw = rem[0];
            auto const chr = lsw < 10 ? '0' + lsw : 'a' + lsw - 10;
            buffer.push_back(static_cast<char>(chr));
            num = div;
        }
        while (num);
        std::ranges::reverse(buffer);

        return buffer;
    }

    inline constexpr uint256_t uint256_t::from_string(char const *const str)
    {
        static constexpr uint256_t MAX_MULTIPLIABLE_BY_10 =
            std::numeric_limits<uint256_t>::max() / 10;
        char const *ptr = str;
        uint256_t result{};
        size_t num_digits = 0;

        if (ptr[0] == '0' && ptr[1] == 'x') {
            ptr += 2;
            size_t const max_digits = sizeof(uint256_t) * 2;
            while (auto const chr = *ptr++) {
                num_digits += 1;
                if (num_digits > max_digits) {
                    throw std::out_of_range(str);
                }
                result = (result << 4) | from_hex(chr);
            }
        }
        else {
            while (auto const chr = *ptr++) {
                num_digits += 1;
                if (result > MAX_MULTIPLIABLE_BY_10) {
                    throw std::out_of_range(str);
                }
                auto const digit = from_dec(chr);
                result = (truncating_mul(result, 10)) + digit;
                if (result < digit) {
                    throw std::out_of_range(str);
                }
            }
        }

        return result;
    }
}

template <>
struct std::formatter<monad::vm::runtime::uint256_t>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::runtime::uint256_t const &v, std::format_context &ctx) const
    {
        return std::format_to(ctx.out(), "0x{}", v.to_string(16));
    }
};
