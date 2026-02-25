#include "/home/malvarez/includes/random.hpp"
#include <bit>
#include <cstdio>
#include <cstring>
#include <immintrin.h>
#include <iostream>
#include <optional>
#include <string>
#include <string_view>
#include <tuple>

// x must have at most 19 digits, i.e. x < 10^19
constexpr uint64_t pow10e19 = 10'000'000'000'000'000'000ULL;

// ============================================================================
// Common tables
// ============================================================================

constexpr auto digits_0_9 = ([]() constexpr {
    std::array<char, 10> digits;
    for (size_t i = 0; i < 10; i++) {
        digits[i] = static_cast<char>('0' + i);
    }
    return digits;
})();

constexpr auto digits_0_99 = ([]() constexpr {
    std::array<char, 200> digits;
    for (size_t i = 0; i < 100; i++) {
        digits[i * 2] = static_cast<char>('0' + i / 10);
        digits[i * 2 + 1] = static_cast<char>('0' + i % 10);
    }
    return digits;
})();

constexpr std::array<uint64_t, 20> pow_10 = []() {
    std::array<uint64_t, 20> table{};
    table[0] = 1;
    for (size_t i = 1; i < 20; i++) {
        table[i] = table[i - 1] * 10;
    }
    return table;
}();

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

inline constexpr size_t num_digits_base10(uint64_t x)
{
    if (x == 0) {
        return 1;
    }
    auto const num_bits = static_cast<size_t>(64 - std::countl_zero(x));
    auto num_digits = (num_bits * 1233) >> 12;
    if (num_digits < 19 && x >= pow_10[num_digits]) {
        num_digits++;
    }
    return num_digits;
}

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

// ============================================================================
// Reference implementation (sprintf)
// ============================================================================

template <bool print_leading_zeros>
[[gnu::noinline]]
void write_base10_sprintf(uint64_t x, std::string &buffer)
{
    char tmp[21];
    int len;
    if constexpr (print_leading_zeros) {
        len = std::sprintf(tmp, "%019lu", x);
    }
    else {
        len = std::sprintf(tmp, "%lu", x);
    }
    buffer.append(tmp, static_cast<size_t>(len));
}

// ============================================================================
// LR printing with switch and base 100
// ============================================================================

template <bool write_leading_zeros>
inline constexpr void write_base10_lr_switch(uint64_t x, std::string &buffer)
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
        buffer[I + i] = digits_0_9[msd];
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

// ============================================================================
// Jeaiii's algo, 32-bit limbs
// ============================================================================

template <bool print_leading_zeros, size_t digits>
inline void write_base10_jeaiii_32(std::uint32_t n, std::string &buffer)
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
inline constexpr void write_base10_jeaiii(uint64_t x, std::string &buffer)
{
    constexpr uint64_t max = 1'000'000'000ul;

    uint32_t high = static_cast<uint32_t>(x / max);
    uint32_t low = static_cast<uint32_t>(x % max);
    write_base10_jeaiii_32<print_leading_zeros, 9>(high, buffer);
    if constexpr (print_leading_zeros) {
        write_base10_jeaiii_32<true, 10>(low, buffer);
    }
    else if (high != 0) {
        write_base10_jeaiii_32<true, 10>(low, buffer);
    }
    else {
        write_base10_jeaiii_32<print_leading_zeros, 10>(low, buffer);
    }
}

// ============================================================================
// SSE: convert 16 decimal digits to ASCII in a single 128-bit register
// ============================================================================

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

// ============================================================================
// Naive RL base 100
// ============================================================================

template <bool print_leading_zeros>
inline constexpr void write_base10_rl(uint64_t x, std::string &buffer)
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
        buffer[I + digits_base10 - 1] = digits_0_9[x % 10];
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

// ============================================================================
// My version of Lemire's method
// ============================================================================

template <bool print_leading_zeros>
inline constexpr void write_base10_alvarez(uint64_t x, std::string &buffer)
{
    // x has at most 19 digits
    assert(x < pow10e19_1);
    size_t I = buffer.length();
    size_t digits_base10;
    if constexpr (print_leading_zeros) {
        digits_base10 = 19;
    }
    else {
        digits_base10 = num_digits_base10_countlz(x);
    }
    buffer.resize(I + digits_base10);

    uint64_t hi;
    uint64_t lo;
    size_t remaining_digits;
    if constexpr (print_leading_zeros) {
        // Process most significant upper 3 digits to get down to 16
        uint64_t d18_16 = x / 10'000'000'000'000'000;
        uint64_t d15_0 = x % 10'000'000'000'000'000;

        hi = d15_0 / 100'000'000;
        lo = x % 100'000'000;

        uint64_t d18 = d18_16 / 100;
        uint64_t d17_16 = d18_16 % 100;
        std::memcpy(&buffer[I + 0], &digits_0_99[d18 * 2 + 1], 1);
        std::memcpy(&buffer[I + 1], &digits_0_99[d17_16 * 2], 2);
        remaining_digits = 16;
    }
    else {
        size_t digits_after_adjustment = digits_base10 & ~size_t(3);
        uint64_t adjustment_divisor = pow_10[digits_after_adjustment];
        switch (digits_base10 & 3) {
        case 0: {
            // Divisible by 4. Nothing to do.
            lo = x;
            break;
        }
        case 1: {
            // 1 extra digit. Process it to get down to a multiple of 4.
            uint64_t d = x / adjustment_divisor;
            lo = x % adjustment_divisor;
            buffer[I + 0] = digits_0_9[d];
            break;
        }
        case 2: {
            // 2 extra digits.
            uint64_t d10 = x / adjustment_divisor;
            lo = x % adjustment_divisor;
            std::memcpy(&buffer[I + 0], &digits_0_99[d10 * 2], 2);
            break;
        }
        case 3: {
            // 3 extra digits.
            uint64_t d210 = x / adjustment_divisor;
            lo = x % adjustment_divisor;
            uint64_t d2 = d210 / 100;
            uint64_t d10 = d210 % 100;
            buffer[I + 0] = digits_0_9[d2];
            std::memcpy(&buffer[I + 1], &digits_0_99[d10 * 2], 2);
            break;
        }
        default:
            // Unreachable
            break;
        }
        remaining_digits = digits_after_adjustment;
        if (remaining_digits == 0) {
            return;
        }
        // Remaining digits is at most 16. We need fast division by 10^8, 10^6,
        // 10^4, or 10^2.
        switch (remaining_digits) {
        case 16:
            hi = lo / 100'000'000;
            lo = x % 100'000'000;
            break;
        case 12:
            hi = lo / 1'000'000;
            lo = x % 1'000'000;
            break;
        case 8:
            hi = lo / 10'000;
            lo = x % 10'000;
            break;
        case 4:
            hi = lo / 100;
            lo = x % 100;
            break;
        default:
            hi = 0;
            // Unreachable
            break;
        }
    }
    size_t const remaining_digits_base100 = remaining_digits / 2;
#pragma GCC unroll 4
    for (size_t i = 0; i < remaining_digits_base100 / 2; i++) {
        uint64_t digit_hi = hi % 100;
        hi /= 100;
        uint64_t digit_lo = lo % 100;
        lo /= 100;
        std::memcpy(
            &buffer[I + digits_base10 - remaining_digits_base100 - 2 - 2 * i],
            &digits_0_99[digit_hi * 2],
            2);
        std::memcpy(
            &buffer[I + digits_base10 - 2 - 2 * i],
            &digits_0_99[digit_lo * 2],
            2);
    }
}

// ============================================================================
// Lemire's method
// ============================================================================

template <bool print_leading_zeros>
inline constexpr void write_base10_lemire(uint64_t x, std::string &buffer)
{
    // x has at most 19 digits
    assert(x < pow10e19_1);
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
        write_base10_rl<false>(x, buffer);
    }
}

// ============================================================================
// Registry
// ============================================================================

using write_fn_t = void (*)(uint64_t, std::string &);

struct Implementation
{
    std::string_view name;
    write_fn_t fn; // print_leading_zeros = false
    write_fn_t fn_lz; // print_leading_zeros = true
};

#define IMPL(name)                                                             \
    {#name, write_base10_##name<false>, write_base10_##name<true>}
static constexpr Implementation implementations[] = {
    IMPL(sprintf),
    IMPL(lr_switch),
    IMPL(alvarez),
    IMPL(lemire),
    IMPL(rl),
    IMPL(sse),
    IMPL(jeaiii),
};

static Implementation const *find_impl(std::string_view name)
{
    for (auto const &impl : implementations) {
        if (impl.name == name) {
            return &impl;
        }
    }
    return nullptr;
}

static void list_implementations()
{
    std::cerr << "Available implementations:" << std::endl;
    for (auto const &impl : implementations) {
        std::cerr << "  " << impl.name << std::endl;
    }
}

// ============================================================================
// Test (fuzz against sprintf reference)
// ============================================================================

static std::optional<std::tuple<uint64_t, std::string, std::string>> fuzz(
    write_fn_t reference, write_fn_t tested, size_t iterations,
    uint64_t max_val = pow10e19)
{
    // Deterministic edge cases first
    constexpr uint64_t edge_cases[] = {
        1,
        9,
        10,
        99,
        100,
        999,
        1000,
        pow_10[9] - 1,
        pow_10[9],
        pow_10[9] + 1,
        pow_10[18] - 1,
        pow_10[18],
        pow_10[18] + 1,
        pow10e19 - 1,
    };

    std::string ref_out, test_out;
    ref_out.reserve(20);
    test_out.reserve(20);

    for (uint64_t x : edge_cases) {
        if (x == 0 || x >= max_val) {
            continue;
        }
        reference(x, ref_out);
        tested(x, test_out);
        if (ref_out != test_out) {
            return {{x, ref_out, test_out}};
        }
        ref_out.clear();
        test_out.clear();
    }

    // Boundary values at each digit-count transition
    for (size_t i = 0; i < 19; i++) {
        for (uint64_t x : {pow_10[i] - 1, pow_10[i], pow_10[i] + 1}) {
            if (x == 0 || x >= max_val) {
                continue;
            }
            reference(x, ref_out);
            tested(x, test_out);
            if (ref_out != test_out) {
                return {{x, ref_out, test_out}};
            }
            ref_out.clear();
            test_out.clear();
        }
    }

    // Random fuzzing
    auto gen = random_generator::from_fixed();
    for (size_t i = 0; i < iterations; i++) {
        uint64_t x = gen.next_i() % max_val;
        if (x == 0) {
            continue;
        }
        reference(x, ref_out);
        tested(x, test_out);
        if (ref_out != test_out) {
            return {{x, ref_out, test_out}};
        }
        ref_out.clear();
        test_out.clear();
    }
    return std::nullopt;
}

// ============================================================================
// Benchmark (use `time` to measure)
// ============================================================================

[[gnu::noinline]]
static size_t
bench(write_fn_t fn, size_t iterations, uint64_t max_val = pow10e19)
{
    auto gen = random_generator::from_fixed();
    std::string buffer;
    buffer.reserve(20);
    size_t total_len = 0;
    for (size_t i = 0; i < iterations; i++) {
        uint64_t x = gen.next_i() % max_val;
        if (x == 0) {
            x = 1;
        }
        fn(x, buffer);
        total_len += buffer.size();
        buffer.clear();
    }
    return total_len;
}

// ============================================================================
// Main
// ============================================================================

static void print_usage(char const *prog)
{
    std::cerr << "Usage:" << std::endl;
    std::cerr << "  " << prog << " test  <impl> <iterations> [--lz] [--max N]"
              << std::endl;
    std::cerr << "  " << prog << " bench <impl> <iterations> [--lz] [--max N]"
              << std::endl;
    std::cerr << std::endl;
    std::cerr << "Options:" << std::endl;
    std::cerr << "  --lz     Enable print_leading_zeros mode (19-digit "
                 "zero-padded output)"
              << std::endl;
    std::cerr << "  --max N  Cap random inputs to [1, N) (default: 10^19)"
              << std::endl;
    std::cerr << std::endl;
    list_implementations();
}

int main(int argc, char *argv[])
{
    if (argc < 4) {
        print_usage(argv[0]);
        return 1;
    }

    std::string_view mode = argv[1];
    std::string_view impl_name = argv[2];

    size_t n_iterations = 0;
    std::sscanf(argv[3], "%lu", &n_iterations);

    bool leading_zeros = false;
    uint64_t max_val = pow10e19;
    for (int i = 4; i < argc; i++) {
        if (std::string_view(argv[i]) == "--lz") {
            leading_zeros = true;
        }
        else if (std::string_view(argv[i]) == "--max" && i + 1 < argc) {
            std::sscanf(argv[++i], "%lu", &max_val);
        }
    }

    auto const *impl = find_impl(impl_name);
    if (!impl) {
        std::cerr << "Unknown implementation: " << impl_name << std::endl;
        list_implementations();
        return 1;
    }

    write_fn_t test_fn = leading_zeros ? impl->fn_lz : impl->fn;

    if (mode == "test") {
        write_fn_t ref_fn =
            leading_zeros
                ? static_cast<write_fn_t>(write_base10_sprintf<true>)
                : static_cast<write_fn_t>(write_base10_sprintf<false>);

        auto result = fuzz(ref_fn, test_fn, n_iterations, max_val);
        if (result) {
            auto const &[x, ref_out, test_out] = *result;
            std::cerr << "Discrepancy found!" << std::endl;
            std::cout << "\tx =               " << x << std::endl;
            std::cout << "\tReference output: " << ref_out << std::endl;
            std::cout << "\tTested output:    " << test_out << std::endl;
            return 1;
        }
        std::cout << "All tests passed (" << n_iterations
                  << " random + edge cases)" << std::endl;
        return 0;
    }

    if (mode == "bench") {
        auto total = bench(test_fn, n_iterations, max_val);
        std::cout << "Total output length: " << total << std::endl;
        return 0;
    }

    std::cerr << "Unknown mode: " << mode << std::endl;
    print_usage(argv[0]);
    return 1;
}
