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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/jumpdest_scan.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

#include <sys/mman.h>
#include <unistd.h>

using namespace monad::vm::interpreter;

using enum monad::vm::compiler::EvmOpCode;

template <typename... Args>
auto make_intercode(Args... args)
{
    return Intercode{std::array<std::uint8_t, sizeof...(args)>{
        static_cast<std::uint8_t>(args)...}};
}

TEST(Intercode, CodeSizeEmpty)
{
    auto const code = make_intercode();
    ASSERT_EQ(code.size(), 0);
}

TEST(Intercode, CodeSizeNonEmpty)
{
    auto const code = make_intercode(PUSH1, 0x01, PUSH0, ADD);
    ASSERT_EQ(code.size(), 4);
}

TEST(Intercode, Code)
{
    auto const ops = std::vector<std::uint8_t>{
        PUSH4,
        0x01,
        0x02,
        0x03,
        0x04,
        JUMP,
        SUB,
        RETURN,
        SELFDESTRUCT,
    };

    auto const code = Intercode(ops);

    for (auto i = 0u; i < ops.size(); ++i) {
        ASSERT_EQ(ops[i], code.code()[i]);
    }
}

TEST(Intercode, Jumpdests)
{
    auto const code = make_intercode(
        JUMPDEST, ADD, SUB, PUSH3, 0x5B, JUMPDEST, JUMPDEST, JUMPDEST);

    ASSERT_TRUE(code.is_jumpdest(0));
    ASSERT_FALSE(code.is_jumpdest(1));
    ASSERT_FALSE(code.is_jumpdest(2));
    ASSERT_FALSE(code.is_jumpdest(3));
    ASSERT_FALSE(code.is_jumpdest(4));
    ASSERT_FALSE(code.is_jumpdest(5));
    ASSERT_FALSE(code.is_jumpdest(6));
    ASSERT_TRUE(code.is_jumpdest(7));
    ASSERT_FALSE(code.is_jumpdest(8));
    ASSERT_FALSE(code.is_jumpdest(3894));
}

// The real scan (SIMD where available) must match a plain reference walk bit
// for bit.
namespace
{
    std::vector<bool> reference_jumpdests(std::vector<std::uint8_t> const &code)
    {
        std::vector<bool> ref(code.size(), false);
        for (std::size_t i = 0; i < code.size(); ++i) {
            auto const op = code[i];
            if (op == JUMPDEST) {
                ref[i] = true;
            }
            if (op >= PUSH1 && op <= PUSH32) {
                i += op - PUSH1 + 1;
            }
        }
        return ref;
    }

    // AVX2 builds never reach the scalar kernel through Intercode.
    std::vector<bool> scalar_jumpdests(std::vector<std::uint8_t> const &code)
    {
        std::vector<std::uint64_t> bits(
            detail::jumpdest_word_count(code.size()), 0);
        detail::find_jumpdests_scalar(code.data(), code.size(), bits.data());
        std::vector<bool> out(code.size(), false);
        for (std::size_t i = 0; i < code.size(); ++i) {
            out[i] = ((bits[i >> 6] >> (i & 63)) & 1) != 0;
        }
        return out;
    }
}

TEST(Intercode, JumpdestScanPushAtEveryOffset)
{
    // The prefix lengths span the SIMD kernel's 16- and 32-byte boundaries.
    for (std::size_t prefix = 0; prefix < 72; ++prefix) {
        for (int k = 1; k <= 32; ++k) {
            for (std::size_t tail = 0; tail <= static_cast<std::size_t>(k) + 36;
                 ++tail) {
                std::vector<std::uint8_t> code(prefix, JUMPDEST);
                code.push_back(static_cast<std::uint8_t>(PUSH1 + k - 1));
                code.insert(code.end(), tail, JUMPDEST);
                auto const ref = reference_jumpdests(code);
                Intercode const ic{code.data(), code.size()};
                for (std::size_t i = 0; i < code.size(); ++i) {
                    ASSERT_EQ(ic.is_jumpdest(i), ref[i])
                        << "size=" << code.size() << " pc=" << i;
                }
                ASSERT_FALSE(ic.is_jumpdest(code.size()));
                ASSERT_EQ(scalar_jumpdests(code), ref)
                    << "size=" << code.size();
            }
        }
    }
}

TEST(Intercode, JumpdestScanTwoPushes)
{
    // A second PUSH starting inside or just after the first.
    for (std::size_t prefix = 0; prefix < 36; ++prefix) {
        for (int k1 = 1; k1 <= 32; ++k1) {
            for (int k2 = 1; k2 <= 32; k2 += 3) {
                for (int gap = 0; gap <= k1 + 1; ++gap) {
                    std::vector<std::uint8_t> code(prefix, JUMPDEST);
                    code.push_back(static_cast<std::uint8_t>(PUSH1 + k1 - 1));
                    code.insert(
                        code.end(), static_cast<std::size_t>(gap), JUMPDEST);
                    code.push_back(static_cast<std::uint8_t>(PUSH1 + k2 - 1));
                    code.insert(code.end(), 36, JUMPDEST);
                    auto const ref = reference_jumpdests(code);
                    Intercode const ic{code.data(), code.size()};
                    for (std::size_t i = 0; i < code.size(); ++i) {
                        ASSERT_EQ(ic.is_jumpdest(i), ref[i])
                            << "size=" << code.size() << " pc=" << i;
                    }
                    ASSERT_FALSE(ic.is_jumpdest(code.size()));
                    ASSERT_EQ(scalar_jumpdests(code), ref)
                        << "size=" << code.size();
                }
            }
        }
    }
}

TEST(Intercode, JumpdestScanUniform)
{
    static constexpr std::uint8_t fills[] = {
        JUMPDEST, PUSH1, PUSH32, STOP, 0xff, PUSH0};
    for (std::size_t len = 0; len < 260; ++len) {
        for (auto const fill : fills) {
            std::vector<std::uint8_t> const code(len, fill);
            auto const ref = reference_jumpdests(code);
            Intercode const ic{code.data(), code.size()};
            for (std::size_t i = 0; i < code.size(); ++i) {
                ASSERT_EQ(ic.is_jumpdest(i), ref[i])
                    << "fill=" << static_cast<int>(fill) << " len=" << len
                    << " pc=" << i;
            }
            ASSERT_FALSE(ic.is_jumpdest(code.size()));
            ASSERT_EQ(scalar_jumpdests(code), ref)
                << "fill=" << static_cast<int>(fill) << " len=" << len;
        }
    }
}

TEST(Intercode, JumpdestScanRandom)
{
    std::mt19937_64 rng(0xBADC0DE);
    for (int t = 0; t < 4000; ++t) {
        std::size_t const len = rng() % 2500;
        std::vector<std::uint8_t> code(len);
        int const push_pct = static_cast<int>(rng() % 60);
        int const jd_pct = static_cast<int>(rng() % 40);
        for (auto &c : code) {
            int const r = static_cast<int>(rng() % 100);
            if (r < push_pct) {
                c = static_cast<std::uint8_t>(PUSH1 + (rng() % 32));
            }
            else if (r < push_pct + jd_pct) {
                c = JUMPDEST;
            }
            else {
                c = static_cast<std::uint8_t>(rng());
            }
        }
        auto const ref = reference_jumpdests(code);
        Intercode const ic{code.data(), code.size()};
        for (std::size_t i = 0; i < code.size(); ++i) {
            ASSERT_EQ(ic.is_jumpdest(i), ref[i])
                << "t=" << t << " size=" << code.size() << " pc=" << i;
        }
        ASSERT_FALSE(ic.is_jumpdest(code.size()));
        ASSERT_EQ(scalar_jumpdests(code), ref)
            << "t=" << t << " size=" << code.size();
    }
}

TEST(Intercode, JumpdestScanLargeAndBoundaries)
{
    // Large inputs carry the entry across many blocks, and sizes straddling
    // 32-byte boundaries exercise the kernel's tail.
    std::mt19937_64 rng(0x5EED);
    std::vector<std::size_t> sizes;
    for (std::size_t const base :
         {std::size_t{0},
          std::size_t{32},
          std::size_t{64},
          std::size_t{256},
          std::size_t{4096}}) {
        for (std::size_t d = 0; d <= 34; ++d) {
            sizes.push_back(base + d);
        }
    }
    sizes.push_back(64 * 1024);
    sizes.push_back(256 * 1024);

    for (std::size_t const n : sizes) {
        std::vector<std::uint8_t> worst(n);
        for (auto &c : worst) {
            c = (rng() & 1) ? JUMPDEST : ADD;
        }
        auto const worst_ref = reference_jumpdests(worst);
        Intercode const worst_ic{worst.data(), worst.size()};
        for (std::size_t i = 0; i < worst.size(); ++i) {
            ASSERT_EQ(worst_ic.is_jumpdest(i), worst_ref[i])
                << "worst size=" << n << " pc=" << i;
        }
        ASSERT_FALSE(worst_ic.is_jumpdest(n));
        ASSERT_EQ(scalar_jumpdests(worst), worst_ref) << "worst size=" << n;
        ASSERT_TRUE(std::ranges::equal(worst_ic.code_span(), worst))
            << "worst size=" << n;
        // Intercode's end padding (end_padding_size).
        for (std::size_t i = 0; i < 33; ++i) {
            ASSERT_EQ(worst_ic.code()[n + i], 0)
                << "worst size=" << n << " i=" << i;
        }

        // PUSH-heavy: immediates hide 0x5b bytes that must not be marked.
        std::vector<std::uint8_t> pushy(n);
        for (auto &c : pushy) {
            int const r = static_cast<int>(rng() % 100);
            if (r < 55) {
                c = static_cast<std::uint8_t>(PUSH1 + (rng() % 32));
            }
            else if (r < 75) {
                c = JUMPDEST;
            }
            else {
                c = static_cast<std::uint8_t>(rng());
            }
        }
        auto const pushy_ref = reference_jumpdests(pushy);
        Intercode const pushy_ic{pushy.data(), pushy.size()};
        for (std::size_t i = 0; i < pushy.size(); ++i) {
            ASSERT_EQ(pushy_ic.is_jumpdest(i), pushy_ref[i])
                << "pushy size=" << n << " pc=" << i;
        }
        ASSERT_FALSE(pushy_ic.is_jumpdest(n));
        ASSERT_EQ(scalar_jumpdests(pushy), pushy_ref) << "pushy size=" << n;
        ASSERT_TRUE(std::ranges::equal(pushy_ic.code_span(), pushy))
            << "pushy size=" << n;
        for (std::size_t i = 0; i < 33; ++i) {
            ASSERT_EQ(pushy_ic.code()[n + i], 0)
                << "pushy size=" << n << " i=" << i;
        }
    }
}

// The code ends where an inaccessible page begins, so a read past the caller's
// code faults in every build, not only under ASan.
TEST(Intercode, JumpdestScanStopsAtCodeEnd)
{
    auto const page = static_cast<std::size_t>(sysconf(_SC_PAGESIZE));
    void *const mem = mmap(
        nullptr,
        2 * page,
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_ANONYMOUS,
        -1,
        0);
    ASSERT_NE(mem, MAP_FAILED);
    auto *const base = static_cast<std::uint8_t *>(mem);
    ASSERT_EQ(mprotect(base + page, page, PROT_NONE), 0);
    std::mt19937_64 rng(0x6A4D);
    for (std::size_t n = 0; n <= page; n += n < 160 ? 1 : 33) {
        std::uint8_t *const code = base + page - n;
        for (std::size_t i = 0; i < n; ++i) {
            code[i] = (rng() & 3) == 0 ? static_cast<std::uint8_t>(JUMPDEST)
                                       : static_cast<std::uint8_t>(rng());
        }
        std::vector<std::uint8_t> const copy(code, code + n);
        auto const ref = reference_jumpdests(copy);
        Intercode const ic{code, n};
        for (std::size_t i = 0; i < n; ++i) {
            ASSERT_EQ(ic.is_jumpdest(i), ref[i]) << "size=" << n << " pc=" << i;
        }
        ASSERT_TRUE(std::ranges::equal(ic.code_span(), copy)) << "size=" << n;
        // Intercode's end padding (end_padding_size).
        for (std::size_t i = 0; i < 33; ++i) {
            ASSERT_EQ(ic.code()[n + i], 0) << "size=" << n << " i=" << i;
        }
    }
    ASSERT_EQ(munmap(mem, 2 * page), 0);
}

#if defined(__AVX2__)
// `src` holds exactly the code, so ASan catches a read past it, and `dst`
// starts as JUMPDEST bytes because Intercode's buffer starts uninitialized.
TEST(Intercode, ScalarAndSimdScansAgree)
{
    std::mt19937_64 rng(0xD1FF);
    for (int t = 0; t < 6000; ++t) {
        std::size_t const n = rng() % 4096;
        std::vector<std::uint8_t> code(
            n + detail::avx2_scan_padding, 0); // what `dst` should hold
        int const push_pct = static_cast<int>(rng() % 60);
        int const jd_pct = static_cast<int>(rng() % 40);
        for (std::size_t i = 0; i < n; ++i) {
            int const r = static_cast<int>(rng() % 100);
            if (r < push_pct) {
                code[i] = static_cast<std::uint8_t>(PUSH1 + (rng() % 32));
            }
            else if (r < push_pct + jd_pct) {
                code[i] = JUMPDEST;
            }
            else {
                code[i] = static_cast<std::uint8_t>(rng());
            }
        }
        std::vector<std::uint8_t> const src(code.data(), code.data() + n);
        std::vector<std::uint8_t> dst(n + detail::avx2_scan_padding, 0);
        std::fill_n(dst.begin(), n, JUMPDEST);
        std::vector<std::uint64_t> scalar_bits(
            detail::jumpdest_word_count(n), 0);
        std::vector<std::uint64_t> simd_bits(detail::jumpdest_word_count(n), 0);
        detail::find_jumpdests_scalar(code.data(), n, scalar_bits.data());
        detail::copy_and_find_jumpdests_avx2(
            src.data(), dst.data(), n, simd_bits.data());
        ASSERT_EQ(scalar_bits, simd_bits) << "t=" << t << " size=" << n;
        ASSERT_EQ(dst, code) << "t=" << t << " size=" << n;
    }

    // Covers the kernel's tail and the entry carried between blocks.
    for (std::size_t n = 0; n <= 160; ++n) {
        std::vector<std::uint8_t> code(n + detail::avx2_scan_padding, 0);
        for (std::size_t i = 0; i < n; ++i) {
            code[i] = static_cast<std::uint8_t>((i * 7 + 3) & 0xff);
        }
        std::vector<std::uint8_t> const src(code.data(), code.data() + n);
        std::vector<std::uint8_t> dst(n + detail::avx2_scan_padding, 0);
        std::fill_n(dst.begin(), n, JUMPDEST);
        std::vector<std::uint64_t> scalar_bits(
            detail::jumpdest_word_count(n), 0);
        std::vector<std::uint64_t> simd_bits(detail::jumpdest_word_count(n), 0);
        detail::find_jumpdests_scalar(code.data(), n, scalar_bits.data());
        detail::copy_and_find_jumpdests_avx2(
            src.data(), dst.data(), n, simd_bits.data());
        ASSERT_EQ(scalar_bits, simd_bits) << "size=" << n;
        ASSERT_EQ(dst, code) << "size=" << n;
    }
}
#endif
