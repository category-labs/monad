#pragma once

#include <monad/vm/core/assert.h>

#include <bit>
#include <cstdint>
#include <format>
#include <immintrin.h>
#include <intx/intx.hpp>
#include <limits>
#include <stdexcept>

#ifndef __AVX2__
    #error "Target architecture must support AVX2"
#endif

namespace monad::vm::runtime
{
    struct uint256_t;
}

// It is assumed that if the `result` pointer overlaps with `left` and/or
// `right`, then `result` pointer is equal to `left` and/or `right`.
extern "C" void monad_vm_runtime_mul(
    monad::vm::runtime::uint256_t *result,
    monad::vm::runtime::uint256_t const *left,
    monad::vm::runtime::uint256_t const *right) noexcept;

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

        template <typename... T>
        [[gnu::always_inline]]
        constexpr explicit(true) uint256_t(::intx::uint256 const &x) noexcept
            : words_{x[0], x[1], x[2], x[3]}
        {
        }

        [[gnu::always_inline]]
        inline ::intx::uint256 const &as_intx() const noexcept
        {
            return *reinterpret_cast<::intx::uint256 const *>(this);
        }

        [[gnu::always_inline]]
        inline constexpr ::intx::uint256 to_intx() const noexcept
        {
            return ::intx::uint256{words_[0], words_[1], words_[2], words_[3]};
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

        // NOLINTBEGIN(bugprone-macro-parentheses)

#define INHERIT_INTX_BINOP(return_ty, op_name)                                 \
    [[gnu::always_inline]] friend inline constexpr return_ty operator op_name( \
        uint256_t const &x, uint256_t const &y) noexcept                       \
    {                                                                          \
        if consteval {                                                         \
            return return_ty(x.to_intx() op_name y.to_intx());                 \
        }                                                                      \
        else {                                                                 \
            return return_ty(x.as_intx() op_name y.as_intx());                 \
        }                                                                      \
    }

        INHERIT_INTX_BINOP(uint256_t, /);
        INHERIT_INTX_BINOP(uint256_t, %);
#undef INHERIT_INTX_BINOP

        // NOLINTEND(bugprone-macro-parentheses)

        [[gnu::always_inline]]
        constexpr friend inline result_with_carry<uint256_t>
        subb(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            auto [w0, b0] = subb(lhs[0], rhs[0], false);
            auto [w1, b1] = subb(lhs[1], rhs[1], b0);
            auto [w2, b2] = subb(lhs[2], rhs[2], b1);
            auto [w3, b3] = subb(lhs[3], rhs[3], b2);
            return {.value = uint256_t{w0, w1, w2, w3}, .carry = b3};
        }

        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        operator+(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            auto [w0, c0] = addc(lhs[0], rhs[0], false);
            auto [w1, c1] = addc(lhs[1], rhs[1], c0);
            auto [w2, c2] = addc(lhs[2], rhs[2], c1);
            auto [w3, c3] = addc(lhs[3], rhs[3], c2);
            return uint256_t{w0, w1, w2, w3};
        }

        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        operator-(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            return subb(lhs, rhs).value;
        }

        [[gnu::always_inline]]
        friend inline constexpr uint256_t
        operator*(uint256_t const &lhs, uint256_t const &rhs) noexcept
        {
            if consteval {
                return uint256_t(lhs.to_intx() * rhs.to_intx());
            }
            else {
                uint256_t result;
                monad_vm_runtime_mul(&result, &lhs, &rhs);
                return result;
            }
        }

        [[gnu::always_inline]]
        inline constexpr uint256_t &operator*=(uint256_t const &rhs) noexcept
        {
            if consteval {
                return *this = *this * rhs;
            }
            else {
                monad_vm_runtime_mul(this, this, &rhs);
                return *this;
            }
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
        inline std::string to_string(int const base0 = 10) const
        {
            MONAD_VM_ASSERT(base0 >= 2 && base0 <= 36);

            auto num = this->to_intx();
            auto const base = ::intx::uint256{base0};

            std::string buffer{};
            do {
                auto const [div, rem] = ::intx::udivrem(num, base);
                auto const lsw = rem[0];
                auto const chr = lsw < 10 ? '0' + lsw : 'a' + lsw - 10;
                buffer.push_back(static_cast<char>(chr));
                num = div;
            }
            while (num);
            std::ranges::reverse(buffer);

            return buffer;
        }

        static inline constexpr uint256_t from_string(char const *s);

        [[gnu::always_inline]] static inline constexpr uint256_t
        from_string(std::string const &s)
        {
            return from_string(s.c_str());
        }
    };

    static_assert(
        alignof(uint256_t) == alignof(::intx::uint256),
        "Alignment of uint256_t is incompatible with intx");
    static_assert(
        sizeof(uint256_t) == sizeof(::intx::uint256),
        "Size of uint256_t is incompatible with intx");

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

    [[gnu::always_inline]] inline constexpr uint32_t
    count_significant_words(uint256_t const &x) noexcept
    {
        for (size_t i = uint256_t::num_words; i > 0; --i) {
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
        auto const significant_words = count_significant_words(x);
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

    struct div_result
    {
        uint256_t quot;
        uint256_t rem;
    };

    [[gnu::always_inline]]
    inline constexpr div_result
    sdivrem(uint256_t const &x, uint256_t const &y) noexcept
    {
        auto const sign_bit = uint64_t{1} << 63;
        auto const x_neg = x[uint256_t::num_words - 1] & sign_bit;
        auto const y_neg = y[uint256_t::num_words - 1] & sign_bit;

        auto const x_abs = x_neg ? -x : x;
        auto const y_abs = y_neg ? -y : y;

        auto const quot_neg = x_neg ^ y_neg;

        ::intx::div_result<::intx::uint256, ::intx::uint256> result;
        if consteval {
            result = ::intx::udivrem(x_abs.to_intx(), y_abs.to_intx());
        }
        else {
            result = ::intx::udivrem(x_abs.as_intx(), y_abs.as_intx());
        }

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

    [[gnu::always_inline]]
    inline constexpr uint256_t addmod(
        uint256_t const &x, uint256_t const &y, uint256_t const &mod) noexcept
    {
        if consteval {
            return uint256_t(
                ::intx::addmod(x.to_intx(), y.to_intx(), mod.to_intx()));
        }
        else {
            return uint256_t(
                ::intx::addmod(x.as_intx(), y.as_intx(), mod.as_intx()));
        }
    }

    [[gnu::always_inline]]
    inline constexpr uint256_t mulmod(
        uint256_t const &x, uint256_t const &y, uint256_t const &mod) noexcept
    {
        if consteval {
            return uint256_t(
                ::intx::mulmod(x.to_intx(), y.to_intx(), mod.to_intx()));
        }
        else {
            return uint256_t(
                ::intx::mulmod(x.as_intx(), y.as_intx(), mod.as_intx()));
        }
    }

    [[gnu::always_inline]] inline constexpr uint256_t
    exp(uint256_t base, uint256_t const &exponent) noexcept
    {
        uint256_t result{1};
        if (base == 2) {
            return result << exponent;
        }

        size_t const sig_words = count_significant_words(exponent);
        for (size_t w = 0; w < sig_words; w++) {
            uint64_t word_exp = exponent[w];
            int32_t significant_bits =
                w + 1 == sig_words ? 64 - std::countl_zero(word_exp) : 64;
            while (significant_bits) {
                if (word_exp & 1) {
                    result *= base;
                }
                base *= base;
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
                result = (result * 10) + digit;
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
