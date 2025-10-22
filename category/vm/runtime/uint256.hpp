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
#include <array>
#include <bit>
#include <climits>
#include <cstdint>
#include <cstring>
#include <format>
#include <immintrin.h>
#include <limits>
#include <span>
#include <stdexcept>
#include <tuple>

#ifndef __AVX2__
    #error "Target architecture must support AVX2"
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

        // For convenience when assigning a result_with_carry with std::tie
        std::tuple<T, bool> tie() const noexcept
        {
            return std::tuple{value, carry};
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
        return result_with_carry{
            .value = sub_borrow, .carry = static_cast<bool>(borrow_out)};
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

    using uint128_t = unsigned __int128;
    using int128_t = __int128;

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

    [[gnu::always_inline]]
    constexpr inline div_result<uint64_t>
    div_constexpr(uint64_t u_hi, uint64_t u_lo, uint64_t const v) noexcept
    {
        auto u = (static_cast<uint128_t>(u_hi) << 64) | u_lo;
        auto quot = static_cast<uint64_t>(u / v);
        auto rem = static_cast<uint64_t>(u % v);
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
            auto w0 = force(words_[0]);
            auto w1 = force(words_[1]);
            auto w2 = force(words_[2]);
            auto w3 = force(words_[3]);
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
            auto [diff, carry] = subb(lhs, rhs);
            // If we do not force the result here, clang replaces the sub/sbb
            // chain with a long series of comparisons and flag logic which is
            // worse
            force(diff[0]);
            force(diff[1]);
            force(diff[2]);
            force(diff[3]);
            return carry;
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
            force(x[0] op_name y[0]),                                          \
            force(x[1] op_name y[1]),                                          \
            force(x[2] op_name y[2]),                                          \
            force(x[3] op_name y[3])};                                         \
    }
        BITWISE_BINOP(uint256_t, &);
        BITWISE_BINOP(uint256_t, |);
        BITWISE_BINOP(uint256_t, ^);
#undef BITWISE_BINOP

        // NOLINTEND(bugprone-macro-parentheses)

        [[gnu::always_inline]] friend inline constexpr bool
        operator==(uint256_t const &x, uint256_t const &y) noexcept
        {
            auto e0 = force(x[0] ^ y[0]);
            auto e1 = force(x[1] ^ y[1]);
            auto e2 = force(x[2] ^ y[2]);
            auto e3 = force(x[3] ^ y[3]);
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
            return uint256_t{
                std::byteswap(words_[3]),
                std::byteswap(words_[2]),
                std::byteswap(words_[1]),
                std::byteswap(words_[0])};
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

    uint256_t signextend(uint256_t const &byte_index, uint256_t const &x);
    uint256_t byte(uint256_t const &byte_index, uint256_t const &x);

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
    inline constexpr std::pair<uint64_t, uint64_t>
    mulx_constexpr(uint64_t const x, uint64_t const y) noexcept
    {
        auto const prod = static_cast<uint128_t>(x) * y;
        auto const hi = static_cast<uint64_t>(prod >> 64);
        auto const lo = static_cast<uint64_t>(prod);
        return {hi, lo};
    }

    [[gnu::always_inline]]
    inline std::pair<uint64_t, uint64_t>
    mulx_intrinsic(uint64_t const x, uint64_t const y) noexcept
    {
        uint64_t hi;
        uint64_t lo;
        asm("mulx %[x], %[lo], %[hi]"
            : [hi] "=r"(hi), [lo] "=r"(lo)
            : [x] "r"(x), [y] "d"(y));
        return {hi, lo};
    }

    [[gnu::always_inline]]
    inline constexpr std::pair<uint64_t, uint64_t>
    mulx(uint64_t const x, uint64_t const y) noexcept
    {
        if consteval {
            return mulx_constexpr(x, y);
        }
        else {
            return mulx_intrinsic(x, y);
        }
    }

    template <size_t M>
    using words_t = std::array<uint64_t, M>;

    [[gnu::always_inline]]
    inline std::tuple<uint64_t, uint64_t, uint64_t> adc_3(
        std::tuple<uint64_t, uint64_t, uint64_t> const x,
        std::tuple<uint64_t, uint64_t> const y) noexcept
    {
        auto [x_2, x_1, x_0] = x;
        auto [y_1, y_0] = y;
        asm("addq %[y_0], %[x_0]\n"
            "adcq %[y_1], %[x_1]\n"
            "adcq $0, %[x_2]"
            : [x_0] "+r"(x_0), [x_1] "+r"(x_1), [x_2] "+r"(x_2)
            : [y_0] "r"(y_0), [y_1] "r"(y_1)
            : "cc");
        return {x_2, x_1, x_0};
    }

    [[gnu::always_inline]]
    inline std::pair<uint64_t, uint64_t>
    adc_2(std::pair<uint64_t, uint64_t> const x, uint64_t const y_0) noexcept
    {
        auto [x_1, x_0] = x;
        asm("addq %[y_0], %[x_0]\n"
            "adcq $0, %[x_1]"
            : [x_0] "+r"(x_0), [x_1] "+r"(x_1)
            : [y_0] "r"(y_0)
            : "cc");
        return {x_1, x_0};
    }

    [[gnu::always_inline]]
    inline std::pair<uint64_t, uint64_t> adc_2(
        std::pair<uint64_t, uint64_t> const x,
        std::pair<uint64_t, uint64_t> const y) noexcept
    {
        auto [x_1, x_0] = x;
        auto [y_1, y_0] = y;
        asm("addq %[y_0], %[x_0]\n"
            "adcq %[y_1], %[x_1]"
            : [x_0] "+r"(x_0), [x_1] "+r"(x_1)
            : [y_0] "r"(y_0), [y_1] "r"(y_1)
            : "cc");
        return {x_1, x_0};
    }

    template <size_t I, size_t R, size_t M>
    [[gnu::always_inline]]
    inline void mul_line_recur(
        words_t<M> const &x, uint64_t const y, words_t<R> &__restrict__ result,
        uint64_t carry) noexcept
    {
        if constexpr (I < std::min(R, M)) {
            if constexpr (I + 1 < R) {
                auto const [hi, lo] = mulx(x[I], y);
                std::tie(carry, result[I]) = adc_2({hi, lo}, carry);
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
        std::tie(carry, result[0]) = mulx(y, x[0]);

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
                auto const [hi, lo] = mulx(x[J + 1], y_i);
                std::tie(c_hi, c_lo, result[I + J]) =
                    adc_3({hi, lo, result[I + J]}, {c_hi, c_lo});
            }
            else if constexpr (I + J + 1 < R) {
                // We only need c_lo
                uint64_t const lo = x[J + 1] * y_i;
                std::tie(c_lo, result[I + J]) =
                    adc_2({lo, result[I + J]}, {c_hi, c_lo});
            }
            else {
                // We're done, we don't need subsequent results
                result[I + J] += c_lo;
            }
            mul_add_line_recur<J + 1, I, R, M>(x, y_i, result, c_hi, c_lo);
        }
        else {
            if constexpr (I + M < R) {
                auto [hi, lo] = adc_2({c_hi, c_lo}, result[I + M - 1]);
                result[I + M - 1] = lo;
                result[I + M] = hi;
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
            std::tie(c_hi, c_lo) = mulx(x[0], y_i);
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
                auto const [hi, lo] = mulx(x[i], y[j]);

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
    [[gnu::always_inline]]
    inline constexpr words_t<R>
    truncating_mul(words_t<M> const &x, words_t<N> const &y) noexcept
        requires(0 < R && 0 < M && 0 < N && R <= M + N)
    {
        if consteval {
            return truncating_mul_constexpr<R>(x, y);
        }
        else {
            return truncating_mul_runtime<R>(x, y);
        }
    }

    MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
    inline constexpr uint256_t
    truncating_mul(uint256_t const &x, uint256_t const &y) noexcept
    {
        return uint256_t{
            truncating_mul<uint256_t::num_words>(x.as_words(), y.as_words())};
    }

    template <size_t M, size_t N>
    MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
    inline constexpr words_t<M + N>
    wide_mul(words_t<M> const &x, words_t<N> const &y) noexcept
    {
        return truncating_mul<M + N>(x, y);
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
            auto ix = static_cast<size_t>(i);
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
            auto ix = static_cast<size_t>(i);
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
#pragma GCC unroll(M)
        for (size_t i = 1; i < M; i++) {
            u_norm[i] = shld(u[i], u[i - 1], normalize_shift);
        }
        u_norm[M] = u[M - 1] >> 1 >> (63 - normalize_shift);

        words_t<N> v_norm;
        v_norm[0] = v[0] << normalize_shift;
#pragma GCC unroll(N)
        for (size_t i = 1; i < N; i++) {
            v_norm[i] = shld(v[i], v[i - 1], normalize_shift);
        }

        knuth_div(m, &u_norm[0], n, &v_norm[0], &result.quot[0]);

#pragma GCC unroll(N)
        for (size_t i = 0; i < N - 1; i++) {
            result.rem[i] = shrd(u_norm[i + 1], u_norm[i], normalize_shift);
        }
        result.rem[N - 1] = u_norm[N - 1] >> normalize_shift;

        return result;
    }

    [[gnu::always_inline]] constexpr inline div_result<uint256_t>
    udivrem(uint256_t const &u, uint256_t const &v) noexcept
    {
        auto r = udivrem(u.as_words(), v.as_words());
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

            auto [result, xy_carry] = addc(x_norm, y_norm);

            // x_norm + y_norm < 2 * mod
            auto const [rem, rem_borrow] = subb(result, mod);
            if (xy_carry || !rem_borrow) {
                // x_norm + y_norm >= mod
                result = rem;
            }
            return result;
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
        auto const prod = wide_mul(u.as_words(), v.as_words());
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

    template <size_t M, size_t N>
    [[gnu::always_inline]]
    inline constexpr result_with_carry<words_t<std::max(M, N)>>
    subb_zx(words_t<M> const &lhs, words_t<N> const &rhs) noexcept
    {
        words_t<std::max(M, N)> result;
        bool borrow = false;
        if constexpr (M < N) {
#pragma GCC unroll(M)
            for (size_t i = 0; i < M; i++) {
                std::tie(result[i], borrow) =
                    subb(lhs[i], rhs[i], borrow).tie();
            }
#pragma GCC unroll(N)
            for (size_t i = M; i < N; i++) {
                std::tie(result[i], borrow) = subb(0UL, rhs[i], borrow).tie();
            }
        }
        else {
#pragma GCC unroll(N)
            for (size_t i = 0; i < N; i++) {
                std::tie(result[i], borrow) =
                    subb(lhs[i], rhs[i], borrow).tie();
            }
#pragma GCC unroll(M)
            for (size_t i = N; i < M; i++) {
                std::tie(result[i], borrow) = subb(lhs[i], 0UL, borrow).tie();
            }
        }
        return {.value = result, .carry = borrow};
    }

    template <size_t R, size_t M, size_t N>
    [[gnu::always_inline]]
    inline constexpr result_with_carry<words_t<R>>
    subb_truncating(words_t<M> const &lhs, words_t<N> const &rhs) noexcept
        requires(0 <= R && R <= std::max(M, N))
    {
        words_t<R> result;
        bool borrow = false;
#pragma GCC unroll(R)
        for (size_t i = 0; i < R; i++) {
            std::tie(result[i], borrow) = subb(lhs[i], rhs[i], borrow).tie();
        }
        return {.value = result, .carry = borrow};
    }

    template <size_t M>
    [[gnu::always_inline]]
    inline constexpr result_with_carry<words_t<M>>
    subb(words_t<M> const &lhs, words_t<M> const &rhs) noexcept
    {
        return subb_truncating<M>(lhs, rhs);
    }

    template <size_t N>
    [[gnu::always_inline]]
    inline constexpr result_with_carry<words_t<N>>
    addc(words_t<N> const &lhs, words_t<N> const &rhs) noexcept
    {
        words_t<N> result;
        bool carry = false;
        for (size_t i = 0; i < N; i++) {
            auto [wi, bi] = addc(lhs[i], rhs[i], carry);
            result[i] = wi;
            carry = bi;
        }
        return {.value = result, .carry = carry};
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

        auto result = udivrem(x_abs, y_abs);

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
    inline constexpr size_t bit_width(uint256_t const &x)
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

    namespace barrett
    {
        struct BarrettParams
        {
            words_t<uint256_t::num_words> min_denominator;
            words_t<uint256_t::num_words> max_denominator;
            size_t input_bits;
            size_t multiplier_bits = 0;
        };

        template <BarrettParams Params>
            requires(
                uint256_t{Params.min_denominator} > 0 &&
                uint256_t{Params.min_denominator} <=
                    uint256_t{Params.max_denominator} &&
                Params.input_bits > 0)
        struct reciprocal
        {
            // Smallest amount of words to represent `bits` bits
            static constexpr size_t min_words(size_t bits) noexcept
            {
                return (bits + 63) / 64;
            }

            static constexpr uint256_t MIN_DENOMINATOR{Params.min_denominator};
            static constexpr uint256_t MAX_DENOMINATOR{Params.max_denominator};
            static constexpr size_t MIN_DENOMINATOR_BITS =
                bit_width(MIN_DENOMINATOR);
            static constexpr size_t MAX_DENOMINATOR_BITS =
                bit_width(MAX_DENOMINATOR);
            static constexpr size_t MAX_DENOMINATOR_WORDS =
                min_words(MAX_DENOMINATOR_BITS);
            static constexpr size_t INPUT_BITS = Params.input_bits;
            static constexpr size_t INPUT_WORDS = min_words(INPUT_BITS);
            static constexpr size_t MULTIPLIER_BITS = Params.multiplier_bits;
            static constexpr size_t MULTIPLIER_WORDS =
                min_words(MULTIPLIER_BITS);
            static constexpr size_t MAX_QUOTIENT_BITS =
                INPUT_BITS + MULTIPLIER_BITS - MIN_DENOMINATOR_BITS + 1;
            static constexpr size_t MAX_QUOTIENT_WORDS =
                min_words(MAX_QUOTIENT_BITS);

            static constexpr size_t SHIFT = INPUT_BITS;
            static constexpr size_t WORD_SHIFT = SHIFT / 64;
            static constexpr size_t BIT_SHIFT = SHIFT % 64;

            static constexpr size_t NUMERATOR_WORDS = []() -> size_t {
                if constexpr (MULTIPLIER_WORDS) {
                    // Numerator will be y * (1 ^ INPUT_BITS)
                    size_t const multiplier_bits = 64 * MULTIPLIER_WORDS;
                    size_t const shifted_multiplier_bits =
                        multiplier_bits + INPUT_BITS;
                    return min_words(shifted_multiplier_bits);
                }
                else {
                    // Numerator is 1 ^ INPUT_BITS
                    return 1 + WORD_SHIFT;
                }
            }();

            // Returns 1 << SHIFT
            static constexpr words_t<NUMERATOR_WORDS> numerator() noexcept
                requires(MULTIPLIER_WORDS == 0)
            {
                words_t<NUMERATOR_WORDS> num{0};
                num[WORD_SHIFT] = 1 << BIT_SHIFT;
                return num;
            }

            // Returns y << SHIFT
            static constexpr words_t<NUMERATOR_WORDS>
            numerator(words_t<MULTIPLIER_WORDS> const &y) noexcept
                requires(MULTIPLIER_WORDS > 0)
            {
                // y << (WORD_SHIFT*64 + BIT_SHIFT)
                words_t<NUMERATOR_WORDS> num{0};
                if constexpr (BIT_SHIFT == 0) {
                    for (size_t i = 0; i < MULTIPLIER_WORDS; i++) {
                        num[i + WORD_SHIFT] = y[i];
                    }
                }
                else {
                    // Currently unused, provided here for completeness
                    num[WORD_SHIFT] = y[0] << BIT_SHIFT;
                    for (size_t i = 0; i < MULTIPLIER_WORDS; i++) {
                        num[i + 1 + WORD_SHIFT] =
                            shld(y[i + 1], y[i], BIT_SHIFT);
                    }
                }
                return num;
            }

            // Maximum number of bits that we need to represent the reciprocal
            // for a denominator in the range [MIN_DENOMINATOR, MAX_DENOMINATOR]
            static constexpr size_t RECIPROCAL_BITS = []() {
                words_t<NUMERATOR_WORDS> max_q;
                if constexpr (MULTIPLIER_WORDS) {
                    // The largest possible reciprocal that we need to fit is
                    // the largest possible multiplier times 2^INPUT_BITS,
                    // divided by the smallest possible denominator
                    words_t<MULTIPLIER_WORDS> max_mult;
                    for (auto &w : max_mult) {
                        w = std::numeric_limits<uint64_t>::max();
                    }
                    max_q =
                        udivrem(numerator(max_mult), MIN_DENOMINATOR.as_words())
                            .quot;
                }
                else {
                    // The largest possible reciprocal that we need to fit is
                    // 2^INPUT_BITS divided by the smallest possible denominator
                    max_q =
                        udivrem(numerator(), MIN_DENOMINATOR.as_words()).quot;
                }
                size_t significant_bits = 0;
                for (size_t i = 0; i < NUMERATOR_WORDS; i++) {
                    size_t const ix = NUMERATOR_WORDS - 1 - i;
                    size_t const bits =
                        static_cast<size_t>(64 - std::countl_zero(max_q[ix]));
                    if (bits) {
                        significant_bits = 64 * ix + bits;
                        break;
                    }
                }
                return significant_bits;
            }();

            static constexpr size_t RECIPROCAL_WORDS =
                min_words(RECIPROCAL_BITS);

            [[gnu::always_inline]]
            static inline constexpr bool
            valid_denominator(uint256_t const &d) noexcept
            {
                return MIN_DENOMINATOR <= d && d <= MAX_DENOMINATOR;
            }

            /**
             * Compute an underapproximation of the reciprocal for use in
             * Barrett reduction for udivrem, addmod and mulmod when all
             * inputs are unknown (mulmod when one of the multiplicands is
             * a constant is covered later)
             *
             * Soundness property:
             *     For all inputs x such that 0 <= x < 2^input_bits,
             *         let q = x / denominator_
             *         let q_hat = floor((x * reciprocal_) / 2^SHIFT)
             *         then q - 1 <= q_hat <= q
             * Auxiliary definitions:
             *     SHIFT := input_bits
             *     reciprocal_ := floor(2^SHIFT / denominator_)
             * For brevity:
             *     d := denominator_
             *     r := reciprocal_
             *     S := SHIFT (= input_bits)
             *
             * Proof of soundness:
             *   1. (2^S / d) - 1 < r <= (2^S / d)
             *   2. ((x*2^S) / d) - x < r*x <= (x*2^S/d) (multiplying by x)
             *   3. (x/d) - (x/2^S) < r*x/2^S <= x/d (dividing by 2^S)
             * But x has at most S bits, therefore x/2^S < 1, hence:
             *   4. x/d - 1 < r*x/2^S <= x/d
             * Let q = x/d, q_hat = floor(r*x/2^S). Then:
             *   5. q_hat <= r*x/2^S < q_hat + 1 (by def. of floor)
             *   6. q - 1 < q_hat + 1 (by 4 and 5)
             *   7. q_hat <= q        (by 4 and 5)
             * Finally we have q_hat <= q < q_hat+2 as desired
             */
            inline explicit(true) reciprocal(uint256_t const &d) noexcept
                requires(MULTIPLIER_WORDS == 0)
                : reciprocal_{}
                , denominator_{}
                , multiplier_{}
            {
                MONAD_VM_DEBUG_ASSERT(valid_denominator(d));
                // numerator = 1 << floor(log2(d)) + 1
                words_t<NUMERATOR_WORDS> numerator{0};
                numerator[WORD_SHIFT] = 1 << BIT_SHIFT;
                auto quot = udivrem(numerator, d.as_words()).quot;
                std::memcpy(&reciprocal_, &quot, sizeof(reciprocal_));
                for (size_t i = RECIPROCAL_WORDS;
                     i < std::tuple_size_v<decltype(quot)>;
                     i++) {
                    MONAD_VM_DEBUG_ASSERT(!quot[i]);
                }
                std::memcpy(&denominator_, &d.as_words(), sizeof(denominator_));
                for (size_t i = MAX_DENOMINATOR_WORDS; i < uint256_t::num_words;
                     i++) {
                    MONAD_VM_DEBUG_ASSERT(!d[i]);
                }
            }

            /**
             * Compute an underapproximation of the reciprocal for use in
             * Barrett reduction for mulmod when one of the multiplicands is
             * a constant
             *
             * Soundness property:
             *     For all inputs x such that 0 <= x < 2^input_bits,
             *         let q = x * y / denominator_
             *         let q_hat = floor((x * reciprocal_) / 2^SHIFT)
             *         then q - 1 <= q_hat <= q
             * Auxiliary definitions:
             *     SHIFT := input_bits
             *     reciprocal_ := floor(y * 2^SHIFT / denominator_)
             * For brevity:
             *     d := denominator_
             *     r := reciprocal_
             *     S := SHIFT (= input_bits)
             *
             * Proof of soundness:
             *   1. (y*2^S / d) - 1 < r <= (y*2^S / d)
             *   2. ((x*y*2^S) / d) - x < r*x <= (x*y*2^S/d) (multiplying by x)
             *   3. (xy/d) - (x/2^S) < r*x/2^S <= xy/d (dividing by 2^S)
             * But x has at most S bits, therefore x/2^S < 1, hence:
             *   4. xy/d - 1 < r*x/2^S <= xy/d
             * Let q = xy/d, q_hat = floor(r*x/2^S). Then:
             *   5. q_hat <= r*x/2^S < q_hat + 1 (by def. of floor)
             *   6. q - 1 < q_hat + 1 (by 4 and 5)
             *   7. q_hat <= q        (by 4 and 5)
             * Finally we have q_hat <= q < q_hat+2 as desired
             */
            inline explicit(true)
                reciprocal(uint256_t const &y, uint256_t const &d) noexcept
                requires(MULTIPLIER_WORDS != 0)
                : reciprocal_{}
                , denominator_{}
                , multiplier_{}
            {
                MONAD_VM_DEBUG_ASSERT(valid_denominator(d));
                auto quot = udivrem(numerator(y.as_words()), d.as_words()).quot;
                std::memcpy(&reciprocal_, &quot, sizeof(reciprocal_));
                for (size_t i = RECIPROCAL_WORDS;
                     i < std::tuple_size_v<decltype(quot)>;
                     i++) {
                    MONAD_VM_DEBUG_ASSERT(!quot[i]);
                }
                std::memcpy(&denominator_, &d.as_words(), sizeof(denominator_));
                for (size_t i = MAX_DENOMINATOR_WORDS; i < uint256_t::num_words;
                     i++) {
                    MONAD_VM_DEBUG_ASSERT(!d[i]);
                }
                std::memcpy(&multiplier_, &y.as_words(), sizeof(multiplier_));
                for (size_t i = MULTIPLIER_WORDS; i < uint256_t::num_words;
                     i++) {
                    MONAD_VM_DEBUG_ASSERT(!y[i]);
                }
            }

            /**
             * For Barrett reduction, we compute the quotient approximant
             *     q_hat = floor((x*reciprocal_) / 2^SHIFT)
             * Under some conditions we can pre-divide x by 2^SHIFT to narrow
             * the multiplications involved. The quantity computed is
             *     q_hat = floor(
             *         floor(x/2^PRE_PRODUCT_SHIFT)*reciprocal_
             *         / 2^POST_PRODUCT_SHIFT
             *     )
             * with SHIFT = PRE_PRODUCT_SHIFT + POST_PRODUCT_SHIFT
             */
            static constexpr size_t PRE_PRODUCT_SHIFT = []() -> size_t {
                if (MULTIPLIER_BITS) {
                    // If there is a multiplier, then we cannot pre-shift the
                    // input as this would mean we're discarding too many bits.
                    // This is because (x - lowest_n_bits_x) / 1^n differs from
                    // x / 1^n by at most 1, but ((x-lowest_n_bits_x)*y)/1^n
                    // doesn't.
                    // We could in principle calculate the number of bits that
                    // can be dropped by looking at the multiplier, but it would
                    // lead to a combinatorial explosion of parameters for
                    // mulmod_const reciprocals
                    return 0;
                }
                // We want PRE_PRODUCT_SHIFT to be the largest number k
                // satisfying
                //   1. (2^k-1) < MIN_DENOMINATOR
                //     * This ensures for any input x, the "truncated" quotient
                //         q_approx = ((x >> k) << k) / MIN_DENOMINATOR
                //       differs from the real quotient
                //         q_real = x / MIN_DENOMINATOR
                //       by at most 1
                //   2. (SHIFT - k) == 0 mod 64
                //     * This ensures that the pre-product shift does not add
                //       any extra shr steps
                size_t max_pre_product_shift = bit_width(MIN_DENOMINATOR) - 1;
                size_t const max_pre_product_shift_64 =
                    max_pre_product_shift % 64;
                size_t const shift_64 = BIT_SHIFT;
                if (max_pre_product_shift_64 > shift_64) {
                    max_pre_product_shift -=
                        (max_pre_product_shift_64 - shift_64);
                }
                return max_pre_product_shift;
            }();
            static constexpr size_t PRE_PRODUCT_WORD_SHIFT =
                PRE_PRODUCT_SHIFT / 64;
            static constexpr size_t PRE_PRODUCT_BIT_SHIFT =
                PRE_PRODUCT_SHIFT % 64;

            static constexpr size_t POST_PRODUCT_SHIFT =
                SHIFT - PRE_PRODUCT_SHIFT;
            static constexpr size_t POST_PRODUCT_WORD_SHIFT =
                POST_PRODUCT_SHIFT / 64;
            static constexpr size_t POST_PRODUCT_BIT_SHIFT =
                POST_PRODUCT_SHIFT % 64;

            /**
             * Shift right by `shift` bits
             * Input size is specified in bits so upper empty words can be
             * truncated from the output when, e.g. shifting a 257-bit input by
             * 1 bit as is the case for addmod
             */
            template <size_t input_bits, size_t shift>
            MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
            words_t<min_words(input_bits - shift)>
            rshift(words_t<min_words(input_bits)> const &input) const noexcept
            {
                constexpr size_t R = min_words(input_bits - shift);
                constexpr size_t bit_shift = shift % 64;
                constexpr size_t word_shift = shift / 64;

                words_t<R> result;
                if constexpr (bit_shift) {
                    for (size_t i = 0; i < R - 1; i++) {
                        result[i] = shrd(
                            input[i + 1 + word_shift],
                            input[i + word_shift],
                            bit_shift);
                    }
                    if constexpr (R + word_shift < min_words(input_bits)) {
                        result[R - 1] = shrd(
                            input[R + word_shift],
                            input[R - 1 + word_shift],
                            bit_shift);
                    }
                    else {
                        result[R - 1] = input[R - 1 + word_shift] >> bit_shift;
                    }
                }
                else {
                    // Better codegen than memcpy due to SROA
                    for (size_t i = 0; i < R; i++) {
                        result[i] = input[i + word_shift];
                    }
                }
                return result;
            }

            /**
             * Maximum number of words needed to hold the approximate remainder.
             * In all cases, we are underestimating the quotient by at most 2.
             * Therefore, we are overestimating the remainder by at most
             * 2*denominator_ which fits in MAX_DENOMINATOR_BITS + 2 bits
             */
            static constexpr size_t MAX_R_HAT_BITS = std::min(
                INPUT_BITS + MULTIPLIER_BITS, MAX_DENOMINATOR_BITS + 2UL);
            static constexpr size_t MAX_R_HAT_WORDS = min_words(MAX_R_HAT_BITS);

            /**
             * Maximum number of words to hold the relevant part of the
             * quotient.
             * Since we only care about the remainder (except for udivrem)
             * and we know that the initial approximant and subsequent
             * refinements will fit in MAX_R_HAT_WORDS, we only need
             * to compute the quotient estimate up to RELEVANT_QUOTIENT_BITS
             * The quotient that we obtain from Barrett reduction is only
             * correct when RELEVANT_QUOTIENT_WORDS == MAX_QUOTIENT_WORDS
             */
            static constexpr size_t RELEVANT_QUOTIENT_BITS =
                std::min(MAX_QUOTIENT_BITS, MAX_R_HAT_BITS);
            static constexpr size_t RELEVANT_QUOTIENT_WORDS =
                min_words(RELEVANT_QUOTIENT_BITS);

            template <size_t R>
            MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
            static inline void copy(
                words_t<R> const &src,
                std::span<uint64_t, uint256_t::num_words> dst) noexcept
            {
#pragma GCC unroll(uint256_t::num_words)
                for (size_t i = 0; i < std::min(R, uint256_t::num_words); i++) {
                    dst[i] = src[i];
                }
            }

            /**
             * Compute the approximate quotient q_hat
             * Operationally, this computes the quantity
             *     q_hat = floor(
             *         floor(x / 2^PRE_PRODUCT_SHIFT) * reciprocal_
             *         / 2^POST_PRODUCT_SHIFT
             *     )
             * If PRE_PRODUCT_SHIFT == 0, then q_hat underapproximates q by at
             * most 1
             * If PRE_PRODUCT_SHIFT != 0, then q_hat underapproximates q by at
             * most 2
             *
             * If need_quotient is false, then the quotient is only computed
             * up to RELEVANT_QUOTIENT_WORDS, which is sufficient to compute
             * the remainder but may truncate non-zero words of the quotient.
             */
            template <bool need_quotient>
            MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
            inline words_t<
                need_quotient ? MAX_QUOTIENT_WORDS : RELEVANT_QUOTIENT_WORDS>
            estimate_q(words_t<INPUT_WORDS> const &x) const noexcept
            {
                auto const x_shift = rshift<INPUT_BITS, PRE_PRODUCT_SHIFT>(x);
                constexpr size_t prod_bits =
                    (need_quotient ? MAX_QUOTIENT_BITS
                                   : RELEVANT_QUOTIENT_BITS) +
                    POST_PRODUCT_SHIFT;
                constexpr size_t prod_words = min_words(prod_bits);
                words_t<prod_words> const prod =
                    truncating_mul<prod_words>(x_shift, reciprocal_);
                auto const q_hat = rshift<prod_bits, POST_PRODUCT_SHIFT>(prod);
                return q_hat;
            }

            template <bool need_quotient = false>
            MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
            inline void reduce(
                words_t<INPUT_WORDS> const &x,
                std::span<uint64_t, need_quotient ? uint256_t::num_words : 0>
                    quot,
                std::span<uint64_t, uint256_t::num_words> rem) const noexcept
            {
                // Let B = PRE_PRODUCT_SHIFT
                // We are approximating the shifted product
                //     floor(r * x / 2^S)
                // by the shifted product
                //     floor(r * floor(x/2^B) / 2^(S - B))
                // As seen in the definition of PRE_PRODUCT_SHIFT, B is chosen
                // so that d > 2^B
                // To see why this is sound, let
                //     q = floor(x / d)
                //     x = x_1 * 2^(S-B) + x_0
                //           where x_1 is (256-S) bits and x_0 is S bits
                //     q1 = floor(x_1 * 2^(256-S) / d)
                //     q1_hat = floor(r * x_1 / 2^B)
                //            = floor((r * x_1*2^B)/2^(S-B))
                // By the correctness proof of the reciprocal above, we know
                //     q1 - 1 <= q1_hat <= q1
                // However, since u_0 < v, we also know q1 <= q <= q1+1 and
                // therefore
                //     q - 2 <= q1_hat <= q
                // This optimization is similar to the version of Barrett
                // reduction described in Modern Computer Arithithmetic.
                auto const q_hat = estimate_q<need_quotient>(x);

                // The bit width of q_hat is often of the form 64*k+1. In
                // principle we could use only the lowest 64*k bits of q_hat
                // for the product and then branch on the MSB and add, but
                // empirically this has no performance impact.
                words_t<MAX_R_HAT_WORDS> const qv =
                    truncating_mul<MAX_R_HAT_WORDS>(q_hat, denominator_);

                // We may have underestimated the quotient by up to 2, so the
                // remainder may need one extra word to fit.
                words_t<MAX_R_HAT_WORDS> r_hat;
                if constexpr (MULTIPLIER_BITS) {
                    auto const xy =
                        truncating_mul<MAX_R_HAT_WORDS>(x, multiplier_);
                    r_hat = subb_truncating<MAX_R_HAT_WORDS>(xy, qv).value;
                }
                else {
                    r_hat = subb_truncating<MAX_R_HAT_WORDS>(x, qv).value;
                }

                auto const [r_1, c_1] = subb_zx(r_hat, denominator_);
                // Returning using memcpy or std::copy prevents SROA
                if (MONAD_VM_LIKELY(c_1)) {
                    // r_hat is correct
                    if constexpr (need_quotient) {
                        copy(q_hat, quot);
                    }
                    copy(r_hat, rem);
                    return;
                }
                // r_hat is off by at least d. If we did not
                // apply the pre-product shift optimization, then it is
                // off by exactly d, otherwise it may be off
                // by up to 2*d
                if constexpr (PRE_PRODUCT_SHIFT) {
                    auto const [r_2, c_2] = subb_zx(r_1, denominator_);
                    if (MONAD_VM_UNLIKELY(!c_2)) {
                        if constexpr (need_quotient) {
                            auto const [q_2, c_2] = addc(q_hat, {2});
                            MONAD_VM_DEBUG_ASSERT(!c_2);
                            copy(q_2, quot);
                        }
                        copy(r_2, rem);
                        return;
                    }
                }
                if constexpr (need_quotient) {
                    auto const [q_1, c_1] = addc(q_hat, {1});
                    MONAD_VM_DEBUG_ASSERT(!c_1);
                    copy(q_1, quot);
                }
                copy(r_1, rem);
            }

            words_t<RECIPROCAL_WORDS> reciprocal_;
            words_t<MAX_DENOMINATOR_WORDS> denominator_;
            words_t<MULTIPLIER_WORDS> multiplier_;
        };

        /**
         * Ranges for reciprocal intervals. These are chosen to minimize
         * the word count of the reciprocal bits in each, reducing the
         * the cost of the input-by-reciprocal multiplication which is
         * the main overhead.
         */
        constexpr size_t RECIPROCAL_INTERVAL_RANGES[3]{65, 129, 193};

        // udivrem_reciprocal_for_range<a, b> works for divisors in [2^a,
        // 2^b)
        template <size_t min_bits, size_t cutoff_bits>
        using udivrem_reciprocal_for_range = reciprocal<{
            .min_denominator = (uint256_t{1} << min_bits).as_words(),
            .max_denominator = ((uint256_t{1} << cutoff_bits) - 1).as_words(),
            .input_bits = 256}>;
        using udivrem_reciprocal_1_65 =
            udivrem_reciprocal_for_range<1, RECIPROCAL_INTERVAL_RANGES[0]>;
        static_assert(udivrem_reciprocal_1_65::RECIPROCAL_BITS == 256);
        static_assert(udivrem_reciprocal_1_65::MAX_DENOMINATOR_BITS == 65);
        static_assert(udivrem_reciprocal_1_65::PRE_PRODUCT_WORD_SHIFT == 0);
        using udivrem_reciprocal_65_129 = udivrem_reciprocal_for_range<
            RECIPROCAL_INTERVAL_RANGES[0], RECIPROCAL_INTERVAL_RANGES[1]>;
        static_assert(udivrem_reciprocal_65_129::RECIPROCAL_BITS == 192);
        static_assert(udivrem_reciprocal_65_129::MAX_DENOMINATOR_BITS == 129);
        static_assert(udivrem_reciprocal_65_129::PRE_PRODUCT_WORD_SHIFT == 1);
        using udivrem_reciprocal_129_193 = udivrem_reciprocal_for_range<
            RECIPROCAL_INTERVAL_RANGES[1], RECIPROCAL_INTERVAL_RANGES[2]>;
        static_assert(udivrem_reciprocal_129_193::RECIPROCAL_BITS == 128);
        static_assert(udivrem_reciprocal_129_193::MAX_DENOMINATOR_BITS == 193);
        static_assert(udivrem_reciprocal_129_193::PRE_PRODUCT_WORD_SHIFT == 2);
        using udivrem_reciprocal_193_256 =
            udivrem_reciprocal_for_range<RECIPROCAL_INTERVAL_RANGES[2], 256>;
        static_assert(udivrem_reciprocal_193_256::RECIPROCAL_BITS == 64);
        static_assert(udivrem_reciprocal_193_256::MAX_DENOMINATOR_BITS == 256);
        static_assert(udivrem_reciprocal_193_256::PRE_PRODUCT_WORD_SHIFT == 3);

        // Catch-all version
        using udivrem_reciprocal = udivrem_reciprocal_for_range<1, 256>;
        static_assert(udivrem_reciprocal::RECIPROCAL_BITS == 256);
        static_assert(udivrem_reciprocal::MAX_DENOMINATOR_BITS == 256);
        static_assert(udivrem_reciprocal::PRE_PRODUCT_WORD_SHIFT == 0);

        // addmod_reciprocal_for_range<a, b> works for divisors in [2^a,
        // 2^b)
        template <size_t min_bits, size_t cutoff_bits>
        using addmod_reciprocal_for_range = reciprocal<{
            .min_denominator = (uint256_t{1} << min_bits).as_words(),
            .max_denominator = ((uint256_t{1} << cutoff_bits) - 1).as_words(),
            .input_bits = 257}>;

        // Addmod benefits slightly from different intervals (boundaries
        // at 66, 130 and 194 bits), but the improvement is negligible (<5%)
        using addmod_reciprocal_1_65 =
            addmod_reciprocal_for_range<1, RECIPROCAL_INTERVAL_RANGES[0]>;
        static_assert(addmod_reciprocal_1_65::RECIPROCAL_BITS == 257);
        static_assert(addmod_reciprocal_1_65::MAX_DENOMINATOR_BITS == 65);
        static_assert(addmod_reciprocal_1_65::PRE_PRODUCT_WORD_SHIFT == 0);
        using addmod_reciprocal_65_129 = addmod_reciprocal_for_range<
            RECIPROCAL_INTERVAL_RANGES[0], RECIPROCAL_INTERVAL_RANGES[1]>;
        static_assert(addmod_reciprocal_65_129::RECIPROCAL_BITS == 193);
        static_assert(addmod_reciprocal_65_129::MAX_DENOMINATOR_BITS == 129);
        static_assert(addmod_reciprocal_65_129::PRE_PRODUCT_WORD_SHIFT == 1);
        using addmod_reciprocal_129_193 = addmod_reciprocal_for_range<
            RECIPROCAL_INTERVAL_RANGES[1], RECIPROCAL_INTERVAL_RANGES[2]>;
        static_assert(addmod_reciprocal_129_193::RECIPROCAL_BITS == 129);
        static_assert(addmod_reciprocal_129_193::MAX_DENOMINATOR_BITS == 193);
        static_assert(addmod_reciprocal_129_193::PRE_PRODUCT_WORD_SHIFT == 2);
        using addmod_reciprocal_193_256 =
            addmod_reciprocal_for_range<RECIPROCAL_INTERVAL_RANGES[2], 256>;
        static_assert(addmod_reciprocal_193_256::RECIPROCAL_BITS == 65);
        static_assert(addmod_reciprocal_193_256::MAX_DENOMINATOR_BITS == 256);
        static_assert(addmod_reciprocal_193_256::PRE_PRODUCT_WORD_SHIFT == 3);

        // Catch-all version
        using addmod_reciprocal = addmod_reciprocal_for_range<1, 256>;
        static_assert(addmod_reciprocal::RECIPROCAL_BITS == 257);
        static_assert(addmod_reciprocal::MAX_DENOMINATOR_BITS == 256);
        static_assert(addmod_reciprocal::INPUT_WORDS == 5);

        // mulmod_reciprocal_for_range<a, b> works for divisors in [2^a,
        // 2^b)
        template <size_t min_bits, size_t cutoff_bits>
        using mulmod_reciprocal_for_range = reciprocal<{
            .min_denominator = (uint256_t{1} << min_bits).as_words(),
            .max_denominator = ((uint256_t{1} << cutoff_bits) - 1).as_words(),
            .input_bits = 512}>;
        using mulmod_reciprocal_1_65 =
            mulmod_reciprocal_for_range<1, RECIPROCAL_INTERVAL_RANGES[0]>;
        static_assert(mulmod_reciprocal_1_65::RECIPROCAL_BITS == 8UL * 64);
        static_assert(mulmod_reciprocal_1_65::MAX_DENOMINATOR_BITS == 65);
        using mulmod_reciprocal_65_129 = mulmod_reciprocal_for_range<
            RECIPROCAL_INTERVAL_RANGES[0], RECIPROCAL_INTERVAL_RANGES[1]>;
        static_assert(mulmod_reciprocal_65_129::RECIPROCAL_BITS == 7UL * 64);
        static_assert(mulmod_reciprocal_65_129::MAX_DENOMINATOR_BITS == 129);
        using mulmod_reciprocal_129_193 = mulmod_reciprocal_for_range<
            RECIPROCAL_INTERVAL_RANGES[1], RECIPROCAL_INTERVAL_RANGES[2]>;
        static_assert(mulmod_reciprocal_129_193::RECIPROCAL_BITS == 6UL * 64);
        static_assert(mulmod_reciprocal_129_193::MAX_DENOMINATOR_BITS == 193);
        using mulmod_reciprocal_193_256 =
            mulmod_reciprocal_for_range<RECIPROCAL_INTERVAL_RANGES[2], 256>;
        static_assert(mulmod_reciprocal_193_256::RECIPROCAL_BITS == 5UL * 64);
        static_assert(mulmod_reciprocal_193_256::MAX_DENOMINATOR_BITS == 256);

        // Catch-all version
        using mulmod_reciprocal = mulmod_reciprocal_for_range<1, 256>;
        static_assert(mulmod_reciprocal::RECIPROCAL_BITS == 512);
        static_assert(mulmod_reciprocal::MAX_DENOMINATOR_BITS == 256);
        static_assert(mulmod_reciprocal::PRE_PRODUCT_WORD_SHIFT == 0);

        // mulmod_const_reciprocal_for_range<a, b> works for divisors in
        // [2^a, 2^b)
        template <size_t min_bits, size_t cutoff_bits>
        using mulmod_const_reciprocal_for_range = reciprocal<{
            .min_denominator = (uint256_t{1} << min_bits).as_words(),
            .max_denominator = ((uint256_t{1} << cutoff_bits) - 1).as_words(),
            .input_bits = 256,
            .multiplier_bits = 256}>;
        using mulmod_const_reciprocal_1_65 =
            mulmod_const_reciprocal_for_range<1, RECIPROCAL_INTERVAL_RANGES[0]>;
        static_assert(
            mulmod_const_reciprocal_1_65::RECIPROCAL_BITS == 8UL * 64 - 1);
        static_assert(mulmod_const_reciprocal_1_65::MAX_DENOMINATOR_BITS == 65);
        using mulmod_const_reciprocal_65_129 =
            mulmod_const_reciprocal_for_range<
                RECIPROCAL_INTERVAL_RANGES[0], RECIPROCAL_INTERVAL_RANGES[1]>;
        static_assert(
            mulmod_const_reciprocal_65_129::RECIPROCAL_BITS == 7UL * 64 - 1);
        static_assert(
            mulmod_const_reciprocal_65_129::MAX_DENOMINATOR_BITS == 129);
        using mulmod_const_reciprocal_129_193 =
            mulmod_const_reciprocal_for_range<
                RECIPROCAL_INTERVAL_RANGES[1], RECIPROCAL_INTERVAL_RANGES[2]>;
        static_assert(
            mulmod_const_reciprocal_129_193::RECIPROCAL_BITS == 6UL * 64 - 1);
        static_assert(
            mulmod_const_reciprocal_129_193::MAX_DENOMINATOR_BITS == 193);
        using mulmod_const_reciprocal_193_256 =
            mulmod_const_reciprocal_for_range<
                RECIPROCAL_INTERVAL_RANGES[2], 256>;
        static_assert(
            mulmod_const_reciprocal_193_256::RECIPROCAL_BITS == 5UL * 64 - 1);
        static_assert(
            mulmod_const_reciprocal_193_256::MAX_DENOMINATOR_BITS == 256);

        // Catch-all version
        using mulmod_const_reciprocal =
            mulmod_const_reciprocal_for_range<1, 256>;
        static_assert(mulmod_const_reciprocal::RECIPROCAL_BITS == 511);
        static_assert(mulmod_const_reciprocal::MAX_DENOMINATOR_BITS == 256);
        static_assert(mulmod_const_reciprocal::PRE_PRODUCT_WORD_SHIFT == 0);

        template <BarrettParams Params>
        [[gnu::always_inline]]
        //[[gnu::noinline]]
        MONAD_VM_NO_VECTORIZE inline div_result<uint256_t> udivrem(
            uint256_t const &u, barrett::reciprocal<Params> const &rec) noexcept
            requires(Params.input_bits == 256)
        {
            div_result<uint256_t> result{.quot = {0}, .rem = {0}};
            auto quot{std::span<uint64_t, uint256_t::num_words>(
                result.quot.as_words())};
            auto rem{std::span<uint64_t, uint256_t::num_words>(
                result.rem.as_words())};
            rec.template reduce<true>(u.as_words(), quot, rem);
            return result;
        }

        template <BarrettParams Params>
        [[gnu::always_inline]]
        MONAD_VM_NO_VECTORIZE inline constexpr div_result<uint256_t> sdivrem(
            uint256_t const &x, bool const denominator_neg,
            barrett::reciprocal<Params> const &rec) noexcept
            requires(Params.input_bits == 256)
        {
            auto const sign_bit = uint64_t{1} << 63;
            bool const x_neg = x[uint256_t::num_words - 1] & sign_bit;

            auto const x_abs = x_neg ? -x : x;

            auto const quot_neg = x_neg ^ denominator_neg;

            auto result = udivrem(x_abs, rec);

            return {
                uint256_t{quot_neg ? -result.quot : result.quot},
                uint256_t{x_neg ? -result.rem : result.rem}};
        }

        template <BarrettParams Params>
        MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
        inline uint256_t addmod(
            uint256_t const &x, uint256_t const &y,
            barrett::reciprocal<Params> const &rec) noexcept
            requires(Params.input_bits >= 257)
        {
            auto const &d = rec.denominator_;
            // When d >= 2^192 and x, y < d we could implement the same
            // optimization as we do for division-based addmod, but the Barrett
            // version is fast enough that branch mispredictions dominate.
            auto const [sum_base, sum_carry] = addc(x, y);
            words_t<5> const sum{
                sum_base[0], sum_base[1], sum_base[2], sum_base[3], sum_carry};

            uint256_t remainder{0};
            auto rem{std::span<uint64_t, uint256_t::num_words>(
                remainder.as_words())};
            rec.reduce(sum, std::span<uint64_t, 0>{}, rem);
            return remainder;
        }

        template <BarrettParams Params>
        MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
        inline uint256_t mulmod(
            uint256_t const &x, uint256_t const &y,
            barrett::reciprocal<Params> const &rec)
            requires(Params.input_bits >= 512)
        {
            uint256_t remainder{0};
            auto xy = wide_mul(x.as_words(), y.as_words());
            auto rem{std::span<uint64_t, uint256_t::num_words>(
                remainder.as_words())};
            rec.reduce(xy, std::span<uint64_t, 0>{}, rem);
            return remainder;
        }

        template <BarrettParams Params>
        MONAD_VM_NO_VECTORIZE [[gnu::always_inline]]
        inline uint256_t
        mulmod_const(uint256_t const &x, barrett::reciprocal<Params> const &rec)
            requires(Params.input_bits >= 256 && Params.multiplier_bits >= 256)
        {
            uint256_t remainder{0};
            auto rem{std::span<uint64_t, uint256_t::num_words>(
                remainder.as_words())};
            rec.reduce(x.as_words(), std::span<uint64_t, 0>{}, rem);
            return remainder;
        }
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
