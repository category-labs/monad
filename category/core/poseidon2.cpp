// Copyright (C) 2026 Category Labs, Inc.
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

// See poseidon2.hpp for where the constants come from and why the vectors
// matter.

#include <category/core/poseidon2.hpp>

#include <cstring>

namespace
{
    constexpr uint64_t GL_P = monad::GOLDILOCKS_P;
    constexpr size_t W = 16;
    constexpr size_t HALF_ROUNDS = 4;
    constexpr size_t N_PARTIAL_ROUNDS = 22;
    constexpr uint64_t DIAG[W] = {
        0xde9b91a467d6afc0ULL,
        0xc5f16b9c76a9be17ULL,
        0x0ab0fef2d540ac55ULL,
        0x3001d27009d05773ULL,
        0xed23b1f906d3d9ebULL,
        0x5ce73743cba97054ULL,
        0x1c3bab944af4ba24ULL,
        0x2faa105854dbafaeULL,
        0x53ffb3ae6d421a10ULL,
        0xbcda9df8884ba396ULL,
        0xfc1273e4a31807bbULL,
        0xc77952573d5142c0ULL,
        0x56683339a819b85eULL,
        0x328fcbd8f0ddc8ebULL,
        0xb5101e303fce9cb7ULL,
        0x774487b8c40089bbULL,
    };
    constexpr uint64_t RC[150] = {
        0x15ebea3fc73397c3ULL, 0xd73cd9fbfe8e275cULL, 0x8c096bfce77f6c26ULL,
        0x4e128f68b53d8feaULL, 0x29b779a36b2763f6ULL, 0xfe2adc6fb65acd08ULL,
        0x8d2520e725ad0955ULL, 0x1c2392b214624d2aULL, 0x37482118206dcc6eULL,
        0x2f829bed19be019aULL, 0x2fe298cb6f8159b0ULL, 0x2bbad982deccdbbfULL,
        0xbad568b8cc60a81eULL, 0xb86a814265baad10ULL, 0xbec2005513b3acb3ULL,
        0x6bf89b59a07c2a94ULL, 0xa25deeb835e230f5ULL, 0x3c5bad8512b8b12aULL,
        0x7230f73c3cb7a4f2ULL, 0xa70c87f095c74d0fULL, 0x6b7606b830bb2e80ULL,
        0x6cd467cfc4f24274ULL, 0xfeed794df42a9b0aULL, 0x8cf7cf6163b7dbd3ULL,
        0x9a6e9dda597175a0ULL, 0xaa52295a684faf7bULL, 0x017b811cc3589d8dULL,
        0x55bfb699b6181648ULL, 0xc2ccaf71501c2421ULL, 0x1707950327596402ULL,
        0xdd2fcdcd42a8229fULL, 0x8b9d7d5b27778a21ULL, 0xac9a05525f9cf512ULL,
        0x2ba125c58627b5e8ULL, 0xc74e91250a8147a5ULL, 0xa3e64b640d5bb384ULL,
        0xf53047d18d1f9292ULL, 0xbaaeddacae3a6374ULL, 0xf2d0914a808b3db1ULL,
        0x18af1a3742bfa3b0ULL, 0x9a621ef50c55bdb8ULL, 0xc615f4d1cc5466f3ULL,
        0xb7fbac19a35cf793ULL, 0xd2b1a15ba517e46dULL, 0x4a290c4d7fd26f6fULL,
        0x4f0cf1bb1770c4c4ULL, 0x548345386cd377f5ULL, 0x33978d2789fddd42ULL,
        0xab78c59deb77e211ULL, 0xc485b2a933d2be7fULL, 0xbde3792c00c03c53ULL,
        0xab4cefe8f893d247ULL, 0xc5c0e752eab7f85fULL, 0xdbf5a76f893bafeaULL,
        0xa91f6003e3d984deULL, 0x099539077f311e87ULL, 0x097ec52232f9559eULL,
        0x53641bdf8991e48cULL, 0x2afe9711d5ed9d7cULL, 0xa7b13d3661b5d117ULL,
        0x5a0e243fe7af6556ULL, 0x1076fae8932d5f00ULL, 0x9b53a83d434934e3ULL,
        0xed3fd595a3c0344aULL, 0x28eff4b01103d100ULL, 0x60400ca3e2685a45ULL,
        0x1c8636beb3389b84ULL, 0xac1332b60e13eff0ULL, 0x2adafcc364e20f87ULL,
        0x79ffc2b14054ea0bULL, 0x3f98e4c0908f0a05ULL, 0xcdb230bc4e8a06c4ULL,
        0x1bcaf7705b152a74ULL, 0xd9bca249a82a7470ULL, 0x91e24af19bf82551ULL,
        0xa62b43ba5cb78858ULL, 0xb4898117472e797fULL, 0xb3228bca606cdaa0ULL,
        0x844461051bca39c9ULL, 0xf3411581f6617d68ULL, 0xf7fd50646782b533ULL,
        0x6ca664253c18fb48ULL, 0x2d2fcdec0886a08fULL, 0x29da00dd799b575eULL,
        0x47d966cc3b6e1e93ULL, 0xde884e9a17ced59eULL, 0xdacf46dc1c31a045ULL,
        0x5d2e3c121eb387f2ULL, 0x51f8b0658b124499ULL, 0x1e7dbd1daa72167dULL,
        0x8275015a25c55b88ULL, 0xe8521c24ac7a70b3ULL, 0x6521d121c40b3f67ULL,
        0xac12de797de135b0ULL, 0xafa28ead79f6ed6aULL, 0x685174a7a8d26f0bULL,
        0xeff92a08d35d9874ULL, 0x3058734b76dd123aULL, 0xfa55dcfba429f79cULL,
        0x559294d4324c7728ULL, 0x7a770f53012dc178ULL, 0xedd8f7c408f3883bULL,
        0x39b533cf8d795fa5ULL, 0x160ef9de243a8c0aULL, 0x431d52da6215fe3fULL,
        0x54c51a2a2ef6d528ULL, 0x9b13892b46ff9d16ULL, 0x263c46fcee210289ULL,
        0xb738c96d25aabdc4ULL, 0x5c33a5203996d38fULL, 0x2626496e7c98d8ddULL,
        0xc669e0a52785903aULL, 0xaecde726c8ae1f47ULL, 0x039343ef3a81e999ULL,
        0x2615ceaf044a54f9ULL, 0x7e41e834662b66e1ULL, 0x4ca5fd4895335783ULL,
        0x64b334d02916f2b0ULL, 0x87268837389a6981ULL, 0x034b75bcb20a6274ULL,
        0x58e658296cc2cd6eULL, 0xe2d0f759acc31df4ULL, 0x81a652e435093e20ULL,
        0x0b72b6e0172eaf47ULL, 0x4aec43cec577d66dULL, 0xde78365b028a84e6ULL,
        0x444e19569adc0ee4ULL, 0x942b2451fa40d1daULL, 0xe24506623ea5bd6cULL,
        0x082854bf2ef7c743ULL, 0x69dbbc566f59d62eULL, 0x248c38d02a7b5cb2ULL,
        0x4f4e8f8c09d15edbULL, 0xd96682f188d310cfULL, 0x6f9a25d56818b54cULL,
        0xb6cefed606546cd9ULL, 0x5bc07523da38a67bULL, 0x7df5a3c35b8111cfULL,
        0xaaa2cc5d4db34bb0ULL, 0x9e673ff22a4653f8ULL, 0xbd8b278d60739c62ULL,
        0xe10d20f6925b8815ULL, 0xf6c87b91dd4da2bfULL, 0xfed623e2f71b6f1aULL,
        0xa0f02fa52a94d0d3ULL, 0xbb5794711b39fa16ULL, 0xd3b94fba9d005c7fULL,
        0x15a26e89fad946c9ULL, 0xf3cb87db8a67cf49ULL, 0x400d2bf56aa2a577ULL,
    };

    inline uint64_t gl_add(uint64_t a, uint64_t b)
    {
        return monad::goldilocks_add(a, b);
    }

    inline uint64_t gl_mul(uint64_t a, uint64_t b)
    {
        unsigned __int128 const x = (unsigned __int128)a * b;
        uint64_t const lo = (uint64_t)x, hi = (uint64_t)(x >> 64);
        uint64_t const hi_hi = hi >> 32, hi_lo = hi & 0xFFFFFFFFULL;
        uint64_t t0 = lo - hi_hi;
        if (lo < hi_hi) {
            t0 -= 0xFFFFFFFFULL;
        }
        uint64_t const t1 = hi_lo * 0xFFFFFFFFULL;
        uint64_t t2 = t0 + t1;
        if (t2 < t0) {
            t2 += 0xFFFFFFFFULL;
        }
        if (t2 >= GL_P) {
            t2 -= GL_P;
        }
        return t2;
    }

    inline uint64_t gl_pow7(uint64_t x)
    {
        uint64_t const x2 = gl_mul(x, x), x4 = gl_mul(x2, x2),
                       x6 = gl_mul(x4, x2);
        return gl_mul(x6, x);
    }

    inline void matmul_m4(uint64_t *s)
    {
        uint64_t const t0 = gl_add(s[0], s[1]), t1 = gl_add(s[2], s[3]);
        uint64_t const t2 = gl_add(gl_add(s[1], s[1]), t1);
        uint64_t const t3 = gl_add(gl_add(s[3], s[3]), t0);
        uint64_t const t1_2 = gl_add(t1, t1), t0_2 = gl_add(t0, t0);
        uint64_t const t4 = gl_add(gl_add(t1_2, t1_2), t3);
        uint64_t const t5 = gl_add(gl_add(t0_2, t0_2), t2);
        s[0] = gl_add(t3, t5);
        s[1] = t5;
        s[2] = gl_add(t2, t4);
        s[3] = t4;
    }

    inline void matmul_external(uint64_t *s)
    {
        for (size_t i = 0; i < W / 4; ++i) {
            matmul_m4(s + i * 4);
        }
        uint64_t stored[4] = {0, 0, 0, 0};
        for (size_t i = 0; i < 4; ++i) {
            for (size_t j = 0; j < W / 4; ++j) {
                stored[i] = gl_add(stored[i], s[j * 4 + i]);
            }
        }
        for (size_t i = 0; i < W; ++i) {
            s[i] = gl_add(s[i], stored[i % 4]);
        }
    }
} // namespace

#ifdef MONAD_ZKVM_ZISK
// On the guest the permutation is ZisK's precompile, not the code below: the
// sponge above it is shared, so a witness generator on the host and the guest
// compute the same digest by construction rather than by agreement.
//
// rd = x0 is correct for THIS port; the same spelling silently transpiles to an
// `or` for add256, so a build that reports no `OP poseidon2` is hashing
// nothing.
extern "C" void monad_poseidon2_16(uint64_t state[16])
{
    asm volatile(".option push\n\t"
                 ".option arch, +zicsr\n\t"
                 "csrs 0x812, %0\n\t"
                 ".option pop"
                 :
                 : "r"(state)
                 : "memory");
}
#else
extern "C" void monad_poseidon2_16(uint64_t state[16])
{
    uint64_t *s = state;
    matmul_external(s);
    for (size_t r = 0; r < HALF_ROUNDS; ++r) {
        for (size_t i = 0; i < W; ++i) {
            s[i] = gl_pow7(gl_add(s[i], RC[r * W + i]));
        }
        matmul_external(s);
    }
    for (size_t r = 0; r < N_PARTIAL_ROUNDS; ++r) {
        s[0] = gl_pow7(gl_add(s[0], RC[HALF_ROUNDS * W + r]));
        uint64_t sum = 0;
        for (size_t i = 0; i < W; ++i) {
            sum = gl_add(sum, s[i]);
        }
        for (size_t i = 0; i < W; ++i) {
            s[i] = gl_add(gl_mul(s[i], DIAG[i]), sum);
        }
    }
    for (size_t r = 0; r < HALF_ROUNDS; ++r) {
        size_t const base = HALF_ROUNDS * W + N_PARTIAL_ROUNDS + r * W;
        for (size_t i = 0; i < W; ++i) {
            s[i] = gl_pow7(gl_add(s[i], RC[base + i]));
        }
        matmul_external(s);
    }
}

#endif // MONAD_ZKVM_ZISK

extern "C" void
monad_poseidon2_256(void const *const in, size_t len, unsigned char out[32])
{
    constexpr size_t DATA_LANES = 11;
    constexpr size_t RATE = DATA_LANES * 8; // 88

    uint64_t st[16];
    st[12] = 0;
    st[13] = 0;
    st[14] = 0;
    st[15] = 0;

    auto const *p = static_cast<unsigned char const *>(in);
    alignas(8) unsigned char blk[RATE];

    for (;;) {
        size_t const take = len < RATE ? len : RATE;
        bool const last = take < RATE;
        unsigned char const *w;
        if (last) {
            std::memcpy(blk, p, take);
            std::memset(blk + take, 0, RATE - take);
            blk[take] = 0x01;
            blk[RATE - 1] |= 0x80;
            w = blk;
        }
        else if ((reinterpret_cast<uintptr_t>(p) & 7u) == 0u) {
            w = p; // already aligned: absorb from the caller's bytes
        }
        else {
            std::memcpy(blk, p, RATE);
            w = blk;
        }

        auto const *q = reinterpret_cast<uint64_t const *>(w);
        uint64_t flags = 0;
        for (size_t e = 0; e < DATA_LANES; ++e) {
            uint64_t v = q[e];
            if (v >= 0xFFFFFFFF00000001ULL) {
                v -= 0xFFFFFFFF00000001ULL;
                flags |= 1ULL << e;
            }
            st[e] = v;
        }
        st[11] = flags;
        monad_poseidon2_16(st);

        if (last) {
            break;
        }
        p += RATE;
        len -= RATE;
    }

    std::memcpy(out, st, 32);
}

namespace monad
{

    bool poseidon2_test_vectors()
    {
        uint64_t v[3][16] = {
            {0},
            {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15},
            {0xFFFFFFFF00000000ULL,
             1,
             0xFFFFFFFEFFFFFFFFULL,
             2,
             3,
             4,
             5,
             6,
             7,
             8,
             9,
             10,
             11,
             12,
             13,
             0xFFFFFFFF00000000ULL},
        };
        // First four lanes of each, from proofman-fields and from the ZisK
        // syscall.
        static uint64_t const want[3][4] = {
            {0xf2b2442ea4d72b98ULL,
             0x08367625af002a12ULL,
             0x41d794a3d56b9451ULL,
             0x533967a2f0a214c8ULL},
            {0x85c54702470d9756ULL,
             0xaa53c7a7d52d9898ULL,
             0x285128096efb0dd7ULL,
             0xf3fde5edd3050ac8ULL},
            {0x05aff2e318df3719ULL,
             0x4cf20041d8703f9dULL,
             0x4a44a97012a8c804ULL,
             0xbd2adf3afceb6631ULL},
        };
        for (size_t k = 0; k < 3; ++k) {
            monad_poseidon2_16(v[k]);
            for (size_t i = 0; i < 4; ++i) {
                if (v[k][i] != want[k][i]) {
                    return false;
                }
            }
        }
        return true;
    }

} // namespace monad
