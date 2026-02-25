#include "/home/malvarez/includes/random.hpp"
#include "category/core/runtime/uint256.hpp"
#include <immintrin.h>

using monad::vm::runtime::uint256_t;

#undef assert
#if true
    #define assert(x)                                                          \
        do {                                                                   \
            if (!(x)) {                                                        \
                std::cerr << "Assertion failed at line " << __LINE__ << ": "   \
                          << #x << std::endl;                                  \
                std::abort();                                                  \
            }                                                                  \
        }                                                                      \
        while (0)
#else
    #define assert(x)                                                          \
        do {                                                                   \
        }                                                                      \
        while (0)
#endif

template <size_t Base>
[[gnu::noinline]] inline constexpr void
to_string_slow(uint256_t const &x, std::string& buffer)
{
    buffer = x.to_string(Base);
}

constexpr uint64_t pow10e19_1 = 10'000'000'000'000'000'000ul; // 10^19
constexpr std::array<uint64_t, 2> pow10e19_2 = ([]() {
    auto pow2 = monad::vm::runtime::exp(pow10e19_1, 2);
    assert(pow2.as_words()[2] == 0);
    assert(pow2.as_words()[3] == 0);
    return std::array<uint64_t, 2>{pow2.as_words()[0], pow2.as_words()[1]};
})();

constexpr std::array<uint256_t, 5> pow10e19 = ([]() {
    std::array<uint256_t, 5> table{};
    table[0] = uint256_t(1);
    for (size_t i = 1; i < 5; i++) {
        table[i] = table[i - 1] * pow10e19_1;
    }
    return table;
})();

constexpr std::array<char, 16> int_to_pow2_digit = ([]() {
    std::array<char, 16> table{};
    for (size_t i = 0; i < 16; i++) {
        table[i] = static_cast<char>(i < 10 ? '0' + i : 'a' + (i - 10));
    }
    return table;
})();

constexpr auto digits_0_9 = ([]() constexpr {
    std::array<char, 10> digits;
    for (size_t i = 0; i < 10; i++) {
        digits[i] = int_to_pow2_digit[i];
    }
    return digits;
})();

constexpr auto digits_0_99 = ([]() constexpr {
    std::array<char, 200> digits;
    for (size_t i = 0; i < 100; i++) {
        digits[i * 2] = int_to_pow2_digit[i / 10];
        digits[i * 2 + 1] = int_to_pow2_digit[i % 10];
    }
    return digits;
})();

constexpr std::array<uint64_t, 19> pow_10{
    1,
    10,
    100,
    1'000,
    10'000,
    100'000,
    1'000'000,
    10'000'000,
    100'000'000,
    1'000'000'000,
    10'000'000'000,
    100'000'000'000,
    1'000'000'000'000,
    10'000'000'000'000,
    100'000'000'000'000,
    1'000'000'000'000'000,
    10'000'000'000'000'000,
    100'000'000'000'000'000,
    1'000'000'000'000'000'000,
};

constexpr std::array<uint64_t, 19> pow_100{
    1,
    100,
    10'000,
    1'000'000,
    100'000'000,
    10'000'000'000,
    1'000'000'000'000,
    100'000'000'000'000,
    10'000'000'000'000'000,
    1'000'000'000'000'000'000,
};

inline constexpr size_t num_digits_base10_countlz(uint64_t x)
{
    assert(x < pow10e19_1);
    auto const num_bits = static_cast<size_t>(64 - std::countl_zero(x));
    auto num_digits = (num_bits * 1233) >> 12;
    if (num_digits < 19 && x >= pow_10[num_digits]) {
        num_digits++;
    }
    assert(num_digits == 19 || x < pow_10[num_digits]);
    assert(x == 0 || x >= pow_10[num_digits - 1]);
    return num_digits;
}

template <bool write_leading_zeros>
inline constexpr void write_to_string_base10_lr(uint64_t x, std::string &buffer)
{
    // THIS FUNCTION IS WRONG, DO NOT USE
    // assert(x < max_pow10_in_uint64_t);
    size_t digits_base10;
    if constexpr (write_leading_zeros) {
        digits_base10 = 19;
    }
    else {
        digits_base10 = num_digits_base10_countlz(x);
    }
    size_t I = buffer.length();
    buffer.resize(I + digits_base10);
    size_t i = 0;
    // std::cout << "digits_base10: " << digits_base10 << std::endl;
    size_t digits_base100 = digits_base10 / 2;
    // std::cout << "digits_base100: " << digits_base100 << std::endl;
    bool extra_digit = digits_base10 % 2;
    if (extra_digit) {
        // std::cout << "extra digit" << std::endl;
        uint64_t msd = x / pow_10[digits_base10 - 1];
        // std::cout << "pow10: " << pow_10[digits_base10 - 1] << std::endl;
        // std::cout << "msd: " << msd << std::endl;
        // assert(msd < 10);
        x -= msd * pow_10[digits_base10 - 1];
        buffer[I + i] = int_to_pow2_digit[msd];
        i++;
    }

    for (int digit = static_cast<int>(digits_base100) - 1; digit >= 0;
         digit--) {
        size_t digit_index = static_cast<size_t>(digit);
        uint64_t msd = x / pow_100[digit_index];
        assert(msd < 100);
        x -= msd * pow_100[digit_index];
        std::memcpy(&buffer[I + i], &digits_0_99[msd * 2], 2);
        i += 2;
    }
}

template <bool print_leading_zeros>
struct WriteBase10LR
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_lr<print_leading_zeros>(x, buffer);
    }
};

[[gnu::always_inline]]
static inline __m128i sse_divmod_10000(__m128i x)
{
    constexpr uint32_t div_multiplier = 0xd1b71759;
    constexpr size_t div_shift = 45;
    __m128i quot =
        _mm_srli_epi64(_mm_mul_epu32(x, _mm_set1_epi32(static_cast<int32_t>(div_multiplier))), div_shift);
    __m128i rem = _mm_sub_epi32(x, _mm_mul_epu32(quot, _mm_set1_epi32(10000)));
    return _mm_or_si128(quot, _mm_slli_epi64(rem, 32));
}

[[gnu::always_inline]]
static inline __m128i sse_divmod_100(__m128i x)
{
    constexpr uint16_t div_multiplier = 0x147b;
    constexpr size_t div_shift = 3;
    __m128i quot = _mm_srli_epi16(_mm_mulhi_epu16(x, _mm_set1_epi16(div_multiplier)), div_shift);
    __m128i rem = _mm_sub_epi16(x, _mm_mullo_epi16(quot, _mm_set1_epi16(100)));
    return _mm_or_si128(quot, _mm_slli_epi32(rem, 16));
}

[[gnu::always_inline]]
static inline __m128i sse_divmod_10(__m128i x)
{
    constexpr uint16_t div_multiplier = 0x199a;
    __m128i quot = _mm_mulhi_epu16(x, _mm_set1_epi16(div_multiplier));
    __m128i rem = _mm_sub_epi16(x, _mm_mullo_epi16(quot, _mm_set1_epi16(10)));
    return _mm_or_si128(quot, _mm_slli_epi16(rem, 8));
}

[[gnu::always_inline]]
static inline __m128i digits16_to_ascii(uint32_t hi, uint32_t lo)
{
    __m128i x = _mm_set_epi64x(lo, hi);

    // 2 base 100'000'000 digits -> 4 base 10'000 digits
    __m128i digits_10000 = sse_divmod_10000(x);

    // 4 base 10'000 digits -> 8 base 100 digits
    __m128i digits_100 = sse_divmod_100(digits_10000);

    // 8 base 100 digits -> 16 base 10 digits
    __m128i digits_10 = sse_divmod_10(digits_100);

    return _mm_add_epi8(digits_10, _mm_set1_epi8('0'));
}

template <bool print_leading_zeros>
inline void write_base10_sse(uint64_t x, std::string &buffer)
{
    size_t digits_base10;
    if constexpr (print_leading_zeros) {
        digits_base10 = 19;
    }
    else {
        digits_base10 = num_digits_base10_countlz(x);
    }
    size_t I = buffer.length();
    buffer.resize(I + digits_base10);

    if constexpr (!print_leading_zeros) {
        if (x < 1000) {
            // Number takes at most 3 digits; print those and return.
            if (x >= 10) {
                // At least two-digit tail
                if (x >= 100) {
                    // Three-digit tail
                    buffer[I + digits_base10 - 3] = digits_0_9[x / 100];
                    x = x % 100;
                }
                std::memcpy(
                    &buffer[I + digits_base10 - 2], &digits_0_99[x * 2], 2);
            }
            else if (x) {
                // One-digit tail
                buffer[I + digits_base10 - 1] = digits_0_9[x];
            }
            return;
        }
    }
    uint64_t head = x / 1000;
    uint64_t tail = x % 1000;

    // Print tail unconditionally
    buffer[I + digits_base10 - 3] = digits_0_9[tail / 100];
    tail = tail % 100;
    std::memcpy(&buffer[I + digits_base10 - 2], &digits_0_99[tail * 2], 2);

    auto head_hi = uint32_t(head / 100'000'000);
    auto head_lo = uint32_t(head % 100'000'000);
    __m128i head_digits = digits16_to_ascii(head_hi, head_lo);

    if constexpr (print_leading_zeros) {
        _mm_storeu_si128(reinterpret_cast<__m128i *>(&buffer[I]), head_digits);
    }
    else {
        alignas(16) char scratch[16];
        _mm_store_si128(reinterpret_cast<__m128i *>(scratch), head_digits);
        std::memcpy(
            &buffer[I], &scratch[16 - (digits_base10 - 3)], digits_base10 - 3);
    }
}

template<bool print_leading_zeros>
struct WriteBase10SSE
{
    [[gnu::always_inline]]
    static inline void write_digits(uint64_t x, std::string &buffer)
    {
        write_base10_sse<print_leading_zeros>(x, buffer);
    }
};

template <bool write_leading_zeros>
inline constexpr void
write_to_string_base10_lr_switch(uint64_t x, std::string &buffer)
{
    // assert(x < max_pow10_in_uint64_t);
    size_t digits_base10;
    if constexpr (write_leading_zeros) {
        digits_base10 = 19;
    }
    else {
        digits_base10 = num_digits_base10_countlz(x);
    }
    size_t I = buffer.length();
    buffer.resize(I + digits_base10);
    size_t i = 0;
    size_t digits_base100 = digits_base10 / 2;
    bool extra_digit = digits_base10 % 2;
    if (extra_digit) {
        uint64_t msd = x / pow_10[digits_base10 - 1];
        x -= msd * pow_10[digits_base10 - 1];
        buffer[I + i] = int_to_pow2_digit[msd];
        i++;
    }

#define CASE(N)                                                                \
    {                                                                          \
        uint64_t msd = x / pow_100[(N) - 1];                                   \
        x -= msd * pow_100[(N) - 1];                                           \
        std::memcpy(&buffer[I + i], &digits_0_99[msd * 2], 2);                 \
        i += 2;                                                                \
    }                                                                          \
    [[fallthrough]];
    switch (digits_base100) {
    case 10:
        CASE(10)
    case 9:
        CASE(9)
    case 8:
        CASE(8)
    case 7:
        CASE(7)
    case 6:
        CASE(6)
    case 5:
        CASE(5)
    case 4:
        CASE(4)
    case 3:
        CASE(3)
    case 2:
        CASE(2)
    case 1:
        CASE(1)
    default:
        break;
    }
}

template <bool print_leading_zeros>
struct WriteBase10LRSwitch
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_lr_switch<print_leading_zeros>(x, buffer);
    }
};

template <bool print_leading_zeros, size_t digits>
inline void
write_to_string_base10_jeaii_32(std::uint32_t n, std::string &buffer)
{
    constexpr auto mask = (std::uint64_t(1) << 57) - 1;
    auto y = n * std::uint64_t(1'441'151'881);
    auto const I = buffer.length();

    size_t num_digits;
    if constexpr (print_leading_zeros) {
        num_digits = digits;
    }
    else {
        num_digits = num_digits_base10_countlz(n);
    }
    buffer.resize(I + num_digits);

    size_t num_digits_base100 = num_digits / 2;
    size_t extra_digit = num_digits % 2;
    size_t skip_digits_base100 = 5 - num_digits_base100 - extra_digit;
    for (size_t i = 0; i < skip_digits_base100; i++) {
        y &= mask;
        y *= 100;
    }
    if (extra_digit) {
        buffer[I + 0] = digits_0_99[size_t(y >> 57) * 2];
        y &= mask;
        y *= 100;
    }
    if constexpr (print_leading_zeros) {
#pragma GCC unroll 5
        for (size_t i = 0; i < num_digits_base100; i++) {
            std::memcpy(
                &buffer[I + 2 * i + extra_digit],
                &digits_0_99[size_t(y >> 57) * 2],
                2);
            y &= mask;
            y *= 100;
        }
    }
    else {
        for (size_t i = 0; i < num_digits_base100; i++) {
            std::memcpy(
                &buffer[I + 2 * i + extra_digit],
                &digits_0_99[size_t(y >> 57) * 2],
                2);
            y &= mask;
            y *= 100;
        }
    }
}

template <bool print_leading_zeros>
inline constexpr void
write_to_string_base10_jeaiii(uint64_t x, std::string &buffer)
{
    constexpr uint64_t max = 1'000'000'000ul;

    uint32_t high = static_cast<uint32_t>(x / max);
    uint32_t low = static_cast<uint32_t>(x % max);
    write_to_string_base10_jeaii_32<print_leading_zeros, 9>(high, buffer);
    if constexpr (print_leading_zeros) {
        write_to_string_base10_jeaii_32<true, 10>(low, buffer);
    }
    else if (high != 0) {
        write_to_string_base10_jeaii_32<true, 10>(low, buffer);
    }
    else {
        write_to_string_base10_jeaii_32<print_leading_zeros, 10>(low, buffer);
    }
}

template <bool print_leading_zeros>
struct WriteBase10Jeaiii
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_jeaiii<print_leading_zeros>(x, buffer);
    }
};

// magick numbers for 16-bit division
#define DIV_10		0x199a	// shift = 0 + 16
#define DIV_100		0x147b	// shift = 3 + 16

// magic number for 32-bit division
#define DIV_10000	0xd1b71759		// shift = 13 + 32

template <bool print_leading_zeros>
inline constexpr void
write_to_string_base10_sse(uint64_t v, std::string &buffer)
{
    size_t digits_base10;
    if constexpr (print_leading_zeros) {
        digits_base10 = 19;
    }
    else {
        digits_base10 = num_digits_base10_countlz(v);
    }
    size_t I = buffer.length();
    buffer.resize(I + digits_base10);
    // v is 16-digit number = abcdefghijklmnop
    const __m128i div_10000 = _mm_set1_epi32(DIV_10000);
    const __m128i mul_10000 = _mm_set1_epi32(10000);
    const int div_10000_shift = 45;

    const __m128i div_100   = _mm_set1_epi16(DIV_100);
    const __m128i mul_100   = _mm_set1_epi16(100);
    const int div_100_shift = 3;

    const __m128i div_10    = _mm_set1_epi16(DIV_10);
    const __m128i mul_10    = _mm_set1_epi16(10);

    const __m128i ascii0    = _mm_set1_epi8('0');

	// can't be easliy done in SSE
	const uint32_t a = v / 100000000; // 8-digit number: abcdefgh
	const uint32_t b = v % 100000000; // 8-digit number: ijklmnop

    //                [ 3 | 2 | 1 | 0 | 3 | 2 | 1 | 0 | 3 | 2 | 1 | 0 | 3 | 2 | 1 | 0 ]
    // x            = [       0       |      ijklmnop |       0       |      abcdefgh ]
    __m128i x = _mm_set_epi64x(b, a);

	// x div 10^4   = [       0       |          ijkl |       0       |          abcd ]
    __m128i x_div_10000;
    x_div_10000 = _mm_mul_epu32(x, div_10000);
    x_div_10000 = _mm_srli_epi64(x_div_10000, div_10000_shift);

    // x mod 10^4   = [       0       |          mnop |       0       |          efgh ]
    __m128i x_mod_10000;
    x_mod_10000 = _mm_mul_epu32(x_div_10000, mul_10000);
    x_mod_10000 = _mm_sub_epi32(x, x_mod_10000);

    // y            = [          mnop |          ijkl |          efgh |          abcd ]
    __m128i y = _mm_or_si128(x_div_10000, _mm_slli_epi64(x_mod_10000, 32));
    
    // y_div_100    = [   0   |    mn |   0   |    ij |   0   |    ef |   0   |    ab ]
    __m128i y_div_100;
    y_div_100 = _mm_mulhi_epu16(y, div_100);
    y_div_100 = _mm_srli_epi16(y_div_100, div_100_shift);

    // y_mod_100    = [   0   |    op |   0   |    kl |   0   |    gh |   0   |    cd ]
    __m128i y_mod_100;
    y_mod_100 = _mm_mullo_epi16(y_div_100, mul_100);
    y_mod_100 = _mm_sub_epi16(y, y_mod_100);

    // z            = [    mn |    op |    ij |    kl |    ef |    gh |    ab |    cd ]
    __m128i z = _mm_or_si128(y_div_100, _mm_slli_epi32(y_mod_100, 16));

    // z_div_10     = [ 0 | m | 0 | o | 0 | i | 0 | k | 0 | e | 0 | g | 0 | a | 0 | c ]
    __m128i z_div_10 = _mm_mulhi_epu16(z, div_10);

    // z_mod_10     = [ 0 | n | 0 | p | 0 | j | 0 | l | 0 | f | 0 | h | 0 | b | 0 | d ]
    __m128i z_mod_10;
    z_mod_10 = _mm_mullo_epi16(z_div_10, mul_10);
    z_mod_10 = _mm_sub_epi16(z, z_mod_10);

    // interleave z_mod_10 and z_div_10 -
    // tmp          = [ m | n | o | p | i | j | k | l | e | f | g | h | a | b | c | d ]
    __m128i tmp = _mm_or_si128(z_div_10, _mm_slli_epi16(z_mod_10, 8));

    // determine number of leading zeros
    uint16_t mask = ~_mm_movemask_epi8(_mm_cmpeq_epi8(tmp, _mm_setzero_si128()));
    uint32_t offset = __builtin_ctz(mask | 0x8000);

    // convert to ascii
    tmp = _mm_add_epi8(tmp, ascii0);

    // and save result
    _mm_storeu_si128((__m128i*)&buffer[I], tmp);
}

template <bool print_leading_zeros>
struct WriteBase10SSE
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_sse<print_leading_zeros>(x, buffer);
    }
};

template <bool print_leading_zeros>
inline constexpr void write_to_string_base10_rl(uint64_t x, std::string &buffer)
{
    size_t digits_base10;
    if constexpr (print_leading_zeros) {
        digits_base10 = 19;
    }
    else {
        digits_base10 = num_digits_base10_countlz(x);
    }
    size_t I = buffer.length();
    buffer.resize(I + digits_base10);
    size_t digits_base100 = digits_base10 / 2;
    bool extra_digit = digits_base10 % 2;
    if (extra_digit) {
        buffer[I + digits_base10 - 1] = int_to_pow2_digit[x % 10];
        x /= 10;
    }
    for (size_t digit = 0; digit < digits_base100; digit++) {
        uint64_t lsd = x % 100;
        x /= 100;
        std::memcpy(
            &buffer[I + digits_base10 - 2 * (digit + 1) - extra_digit],
            &digits_0_99[lsd * 2],
            2);
    }
}

template <bool print_leading_zeros>
struct WriteBase10RL
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_rl<print_leading_zeros>(x, buffer);
    }
};

constexpr std::array<uint64_t, 20> pow10 = []() {
    std::array<uint64_t, 20> table{};
    table[0] = 1;
    for (size_t i = 1; i < 20; i++) {
        table[i] = table[i - 1] * 10;
    }
    return table;
}();

template <bool print_leading_zeros>
inline constexpr void
write_to_string_base10_alvarez(uint64_t x, std::string &buffer)
{
    // x has at most 19 digits
    assert( x < pow10e19_1 );
    size_t I = buffer.length();
    if constexpr (print_leading_zeros) {
        buffer.resize(I + 19);
        uint64_t w18_16 = x / 10'000'000'000'000'000;
        uint64_t w15_0 = x % 10'000'000'000'000'000;

        uint64_t w_hi = w15_0 / 100'000'000;
        uint64_t w_lo = x % 100'000'000;

        uint64_t w18 = w18_16 / 100;
        uint64_t w17_16 = w18_16 % 100;
        std::memcpy(&buffer[I + 0], &digits_0_99[w18 * 2 + 1], 1);
        std::memcpy(&buffer[I + 1], &digits_0_99[w17_16 * 2], 2);
        size_t index_hi = I + 6 + 3;
        size_t index_lo = index_hi + 8;
        #pragma GCC unroll 8
        for (size_t i = 0; i < 4; i++) {
            uint64_t digit_hi = w_hi % 100;
            w_hi /= 100;
            uint64_t digit_lo = w_lo % 100;
            w_lo /= 100;
            std::memcpy(&buffer[index_hi - 2 * i], &digits_0_99[digit_hi * 2], 2);
            std::memcpy(&buffer[index_lo - 2 * i], &digits_0_99[digit_lo * 2], 2);
        }
    }
    else {
        /*
        size_t digits_base10 = num_digits_base10_countlz(x);
        buffer.resize(I + digits_base10);
        // Single loop until a power of two does fewer multiplications but has less parallelism
        if (digits_base10 % 2) {
            buffer[I + digits_base10 - 1] = int_to_pow2_digit[x % 10];
            x /= 10;
        }
        size_t half_digits = digits_base10 / 2;
        uint64_t hi = x / pow_100[half_digits];
        uint64_t lo = x % pow_100[half_digits];
        for (size_t i = 0; i < half_digits / 2; i++) {
        }
        */
        write_to_string_base10_rl<false>(x, buffer);
    }
}

template <bool print_leading_zeros>
struct WriteBase10Alvarez
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_alvarez<print_leading_zeros>(x, buffer);
    }
};

template <bool print_leading_zeros>
inline constexpr void
write_to_string_base10_lemire(uint64_t x, std::string &buffer)
{
    // x has at most 19 digits
    assert( x < pow10e19_1 );
    size_t I = buffer.length();
    if constexpr (print_leading_zeros) {
        buffer.resize(I + 19);
        uint64_t w18_8 = x / 100'000'000;
        uint64_t w7_0 = x % 100'000'000;
        uint64_t w18_12 = w18_8 / 10'000;
        uint64_t w11_8 = w18_8 % 10'000;
        uint64_t w7_4 = w7_0 / 10'000;
        uint64_t w3_0 = w7_0 % 10'000;
        uint64_t w18_14 = w18_12 / 100;
        uint64_t w18_18 = w18_14 / 10'000;
        uint64_t w17_14 = w18_14 % 10'000;
        uint64_t w17_16 = w17_14 / 100;
        uint64_t w15_14 = w17_14 % 100;
        uint64_t w13_12 = w18_12 % 100;
        uint64_t w11_10 = w11_8 / 100;
        uint64_t w9_8 = w11_8 % 100;
        uint64_t w7_6 = w7_4 / 100;
        uint64_t w5_4 = w7_4 % 100;
        uint64_t w3_2 = w3_0 / 100;
        uint64_t w1_0 = w3_0 % 100;
        std::memcpy(&buffer[I + 0], &digits_0_99[w18_18 * 2 + 1], 1);
        std::memcpy(&buffer[I + 1], &digits_0_99[w17_16 * 2], 2);
        std::memcpy(&buffer[I + 3], &digits_0_99[w15_14 * 2], 2);
        std::memcpy(&buffer[I + 5], &digits_0_99[w13_12 * 2], 2);
        std::memcpy(&buffer[I + 7], &digits_0_99[w11_10 * 2], 2);
        std::memcpy(&buffer[I + 9], &digits_0_99[w9_8 * 2], 2);
        std::memcpy(&buffer[I + 11], &digits_0_99[w7_6 * 2], 2);
        std::memcpy(&buffer[I + 13], &digits_0_99[w5_4 * 2], 2);
        std::memcpy(&buffer[I + 15], &digits_0_99[w3_2 * 2], 2);
        std::memcpy(&buffer[I + 17], &digits_0_99[w1_0 * 2], 2);
    }
    else {
        /*
        size_t digits_base10 = num_digits_base10_countlz(x);
        buffer.resize(I + digits_base10);
        */
        write_to_string_base10_rl<false>(x, buffer);
    }
}

template <bool print_leading_zeros>
struct WriteBase10Lemire
{
    [[gnu::always_inline]]
    static inline constexpr void write_digits(uint64_t x, std::string &buffer)
    {
        write_to_string_base10_lemire<print_leading_zeros>(x, buffer);
    }
};


template <template <bool print_leading_zeros> typename Writer>
[[gnu::noinline]]
inline constexpr void
to_string_base10_variable_faster(uint256_t const &x, std::string &buffer)
{
    auto const num_bits = bit_width(x);
    if (num_bits == 0) {
        buffer = "0";
        return;
    }
    buffer.reserve(1 + (num_bits * 1233 >> 12)); // log10(2) ~= 1233/4096

    if (x < pow10e19[3]) {
        assert(!x[3]);
        if (x < pow10e19[1]) {
            Writer<false>::write_digits(x[0], buffer);
        }
        else {
            if (x < pow10e19[2]) {
                assert(!x[2]);
                std::array<uint64_t, 2> x_words{x[0], x[1]};
                auto [w1, w0] =
                    monad::vm::runtime::long_div<2>(x_words, pow10e19_1);
                assert(w1[0]);
                Writer<false>::write_digits(w1[0], buffer);
                Writer<true>::write_digits(w0, buffer);
            }
            else {
                assert(!x[3]);
                std::array<uint64_t, 3> x_words{x[0], x[1], x[2]};
                auto [w21_, w0] =
                    monad::vm::runtime::long_div<3>(x_words, pow10e19_1);
                std::array<uint64_t, 2> w21{w21_[0], w21_[1]};
                auto [w2, w1] =
                    monad::vm::runtime::long_div<2>(w21, pow10e19_1);
                assert(w2[0]);
                Writer<false>::write_digits(w2[0], buffer);
                Writer<true>::write_digits(w1, buffer);
                Writer<true>::write_digits(w0, buffer);
            }
        }
    }
    else {
        std::array<uint64_t, 4> const &x_words = x.as_words();
        if (x < pow10e19[4]) {
            auto [hi_, lo_] = monad::vm::runtime::udivrem(x_words, pow10e19_2);

            auto hi = std::array<uint64_t, 2>{hi_[0], hi_[1]};
            auto [w3, w2] = monad::vm::runtime::long_div(hi, pow10e19_1);
            assert(w3[0]);
            Writer<false>::write_digits(w3[0], buffer);
            Writer<true>::write_digits(w2, buffer);

            auto lo = std::array<uint64_t, 2>{lo_[0], lo_[1]};
            auto [w1, w0] = monad::vm::runtime::long_div(lo, pow10e19_1);
            Writer<true>::write_digits(w1[0], buffer);
            Writer<true>::write_digits(w0, buffer);
        }
        else {
            auto [hi_, lo_] = monad::vm::runtime::udivrem(x_words, pow10e19_2);
            assert(!hi_[3]);

            auto hi = std::array<uint64_t, 3>{hi_[0], hi_[1], hi_[2]};
            auto [w43, w2] = monad::vm::runtime::long_div(hi, pow10e19_1);
            auto [w4, w3] = monad::vm::runtime::long_div(w43, pow10e19_1);
            Writer<false>::write_digits(w4[0], buffer);
            Writer<true>::write_digits(w3, buffer);
            Writer<true>::write_digits(w2, buffer);

            auto lo = std::array<uint64_t, 2>{lo_[0], lo_[1]};
            auto [w1, w0] = monad::vm::runtime::long_div(lo, pow10e19_1);
            Writer<true>::write_digits(w1[0], buffer);
            Writer<true>::write_digits(w0, buffer);
        }
    }
}

template <auto reference, auto tested>
std::optional<std::tuple<uint256_t, std::string, std::string>>
fuzz(size_t iterations)
{
    auto gen = random_generator::from_fixed();
    std::string reference_output;
    std::string tested_output;
    reference_output.reserve(100);
    tested_output.reserve(100);

    for (size_t i = 0; i < iterations; i++) {
        uint64_t const bit_width = gen.next_i() % 257;
        uint256_t const x = gen.next_b<uint256_t>(bit_width);

        reference(x, reference_output);
        tested(x, tested_output);
        if (reference_output != tested_output) {
            return {{x, reference_output, tested_output}};
        }
        reference_output.clear();
        tested_output.clear();
        //reference_output = "";
        //tested_output = "";
    }
    return std::nullopt;
}

template <auto reference>
std::optional<std::tuple<uint256_t, std::string, std::string>>
bench(size_t iterations)
{
    return fuzz<reference, reference>(iterations);
}

int main(int argc, char *argv[])
{
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " <n_iterations>" << std::endl;
        return 1;
    }
    size_t n_iterations = 0;
    sscanf(argv[1], "%lu", &n_iterations);

    #if false
    auto const result = bench<
        //to_string_base10_variable_faster<WriteBase10Lemire>
        to_string_base10_variable_faster<WriteBase10SSE>
        //to_string_base10_variable_faster<WriteBase10RL>
        //to_string_base10_variable_faster<WriteBase10Alvarez>
        //to_string_base10_variable_faster<WriteBase10LRSwitch>
        //to_string_base10_variable_faster<WriteBase10Jeaiii>
        //to_string_slow<10>
        >(n_iterations);
    #else
    auto const result = fuzz<
        //to_string_base10_variable_faster<WriteBase10Alvarez>,
        to_string_base10_variable_faster<WriteBase10SSE>,
        to_string_slow<10>
        >(n_iterations);
    #endif
    if (result) {
        auto const &[x, reference_output, tested_output] = *result;
        std::cerr << "Discrepancy found" << std::endl;
        std::cout << "\tx =               " << x.to_string(16) << std::endl;
        std::cout << "\tReference output: " << reference_output << std::endl;
        std::cout << "\tTested output:    " << tested_output << std::endl;
        return 1;
    }
    else {
        std::cout << "All tests passed successfully" << std::endl;
        return 0;
    }
}
