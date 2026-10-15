#include <category/core/runtime/uint256.hpp>
#include <cstdio>
#ifdef __SIZEOF_INT128__
#error "expected the portable paths"
#endif
using u128 = unsigned __int128;
int main() {
    const uint64_t vs[] = {1, 2, 3, 0xffffffffull, 0x100000000ull, 0x100000001ull, 0x7fffffffffffffffull,
        0x8000000000000000ull, 0x8000000000000001ull, 0xffffffff00000000ull, 0xffffffff00000001ull,
        0xfffffffeffffffffull, 0xffffffffffffffffull, 0x80000000ffffffffull, 0x80000000ull, 0x1234567800000000ull,
        0xffff0000ffff0000ull, 0x0000ffffffff0000ull};
    const uint64_t los[] = {0, 1, 0xffffffffull, 0x100000000ull, 0x8000000000000000ull, 0xffffffffffffffffull, 0x123456789abcdef0ull};
    long n = 0, fails = 0;
    for (uint64_t v : vs) {
        uint64_t his[] = {0, 1, v / 2, v - 1, v > 1 ? v - 2 : 0, v >> 32, (v - 1) & 0xffffffff00000000ull};
        for (uint64_t h : his) {
            if (h >= v) continue;
            for (uint64_t l : los) {
                auto d = monad::uint256::portable::div(h, l, v);
                u128 u = ((u128)h << 64) | l; ++n;
                if (d.quot != (uint64_t)(u / v) || d.rem != (uint64_t)(u % v)) { if (fails++ < 10) printf("FAIL %llx:%llx / %llx\n", (unsigned long long)h, (unsigned long long)l, (unsigned long long)v); }
            }
        }
    }
    // divlu32 exhaustive-ish on edge digits
    const uint32_t ds[] = {1, 2, 3, 0xffff, 0x10000, 0x10001, 0x7fffffff, 0x80000000, 0x80000001, 0xffff0000, 0xffffffff, 0xfffeffff};
    for (uint32_t v : ds) for (uint32_t u1 : {0u, 1u, v / 2, v - 1}) for (uint32_t u0 : {0u, 1u, 0xffffu, 0x10000u, 0x80000000u, 0xffffffffu}) {
        if (u1 >= v) continue;
        uint32_t r; uint32_t q = monad::uint256::portable::divlu32(u1, u0, v, r);
        uint64_t u = ((uint64_t)u1 << 32) | u0; ++n;
        if (q != (uint32_t)(u / v) || r != (uint32_t)(u % v)) { if (fails++ < 20) printf("divlu32 FAIL %x:%x / %x\n", u1, u0, v); }
    }
    printf("%ld edge checks, %ld failures\n", n, fails);
    return fails != 0;
}
