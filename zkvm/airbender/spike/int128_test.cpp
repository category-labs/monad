// Spike check, run on the host:
//   clang++ -std=c++23 -O2 -U__SIZEOF_INT128__ -DNDEBUG -I<repo>/zkvm -I<repo> \
//     -I<repo>/third_party/evmc/include -idirafter /opt/homebrew/include \
//     int128_test.cpp int128_test_halt.cpp -o int128_test && ./int128_test
// Host check of the no-__int128 paths (compiled with -U__SIZEOF_INT128__):
// portable div/mulx, knuth_div through uint256 division, and uint128_t ops,
// against unsigned __int128 references (the type itself stays available).
#include <category/core/runtime/uint128.hpp>
#include <category/core/runtime/uint256.hpp>
#include <cstdio>
#include <random>
#ifdef __SIZEOF_INT128__
#error "expected the portable paths"
#endif
using u128 = unsigned __int128;
using monad::uint256_t;
static std::mt19937_64 rng(20261015);
static uint64_t r64() {
    switch (rng() % 6) {           // bias towards edge shapes
    case 0: return 0;
    case 1: return ~uint64_t{0};
    case 2: return uint64_t{1} << (rng() % 64);
    case 3: return rng() >> (rng() % 64);
    default: return rng();
    }
}
int main() {
    long fails = 0, n = 0;
    for (int i = 0; i < 2000000; ++i) {
        uint64_t x = r64(), y = r64();
        uint64_t hi, lo;
        monad::uint256::portable::mulx(x, y, hi, lo);
        u128 p = (u128)x * y; ++n;
        if (hi != (uint64_t)(p >> 64) || lo != (uint64_t)p) { if (fails++ < 5) printf("mulx %llx %llx\n", (unsigned long long)x, (unsigned long long)y); }
        uint64_t v = r64(); if (v == 0) v = 1;
        uint64_t uh = r64() % v, ul = r64();
        auto d = monad::uint256::portable::div(uh, ul, v);
        u128 u = ((u128)uh << 64) | ul; ++n;
        if (d.quot != (uint64_t)(u / v) || d.rem != (uint64_t)(u % v)) { if (fails++ < 5) printf("div %llx:%llx / %llx\n", (unsigned long long)uh, (unsigned long long)ul, (unsigned long long)v); }
        // uint128_t
        monad::uint128_t a{r64(), r64()}, b{r64(), r64()};
        u128 A = ((u128)a.hi << 64) | a.lo, B = ((u128)b.hi << 64) | b.lo;
        auto m = a * b; u128 M = A * B; ++n;
        if (m.lo != (uint64_t)M || m.hi != (uint64_t)(M >> 64)) { if (fails++ < 5) printf("u128 mul\n"); }
        uint64_t dv = r64(); if (dv == 0) dv = 7;
        auto q = a / dv; u128 Q = A / dv; ++n;
        if (q.lo != (uint64_t)Q || q.hi != (uint64_t)(Q >> 64)) { if (fails++ < 5) printf("u128 div\n"); }
        unsigned s = rng() % 128; auto sh = a >> s; u128 S = A >> s; ++n;
        if (sh.lo != (uint64_t)S || sh.hi != (uint64_t)(S >> 64)) { if (fails++ < 5) printf("u128 shr %u\n", s); }
    }
    // uint256 division (knuth_div for multi-word divisors, long_div otherwise)
    for (int i = 0; i < 400000; ++i) {
        uint256_t a{r64(), r64(), r64(), r64()};
        uint256_t b{r64(), rng() % 3 ? r64() : 0, rng() % 2 ? r64() : 0, rng() % 2 ? r64() : 0};
        if (b == 0) b = 3;
        uint256_t q = a / b, r = a % b; ++n;
        if (!(r < b) || q * b + r != a) { if (fails++ < 10) printf("u256 div fail %d\n", i); }
    }
    // to_string / from_string round trips
    for (int i = 0; i < 20000; ++i) {
        monad::uint128_t a{r64(), r64()};
        std::string s10 = monad::to_string(a), s16 = "0x" + monad::to_string(a, 16);
        u128 A = ((u128)a.hi << 64) | a.lo; std::string ref; u128 t = A;
        if (t == 0) ref = "0"; while (t) { ref.insert(ref.begin(), char('0' + (int)(t % 10))); t /= 10; }
        auto b10 = monad::uint128_t::from_string(s10.c_str()), b16 = monad::uint128_t::from_string(s16.c_str()); ++n;
        if (s10 != ref || !(b10 == a) || !(b16 == a)) { if (fails++ < 5) printf("string %s vs %s\n", s10.c_str(), ref.c_str()); }
    }
    printf("%ld checks, %ld failures\n", n, fails);
    return fails != 0;
}
