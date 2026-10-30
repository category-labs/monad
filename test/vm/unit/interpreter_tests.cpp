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

#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

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

// Differential check: the real scan (SIMD where available) must agree bit for
// bit with a plain reference walk, since a wrong bit is a consensus fault.
namespace
{
    std::vector<bool> reference_jumpdests(std::vector<std::uint8_t> const &code)
    {
        std::vector<bool> ref(code.size(), false);
        for (std::size_t i = 0; i < code.size(); ++i) {
            auto const op = code[i];
            if (op == static_cast<std::uint8_t>(JUMPDEST)) {
                ref[i] = true;
            }
            if (op >= static_cast<std::uint8_t>(PUSH1) &&
                op <= static_cast<std::uint8_t>(PUSH32)) {
                i += op - static_cast<std::uint8_t>(PUSH1) + 1;
            }
        }
        return ref;
    }
}

TEST(Intercode, JumpdestScanPushAtEveryOffset)
{
    // Every PUSH length at every offset around the 16- and 32-byte block
    // boundaries the SIMD kernel uses, JUMPDEST-padded on both sides, cut at
    // every tail length past the immediate.
    for (std::size_t prefix = 0; prefix < 72; ++prefix) {
        for (int k = 1; k <= 32; ++k) {
            for (std::size_t tail = 0; tail <= static_cast<std::size_t>(k) + 36;
                 ++tail) {
                std::vector<std::uint8_t> code(
                    prefix, static_cast<std::uint8_t>(JUMPDEST));
                code.push_back(
                    static_cast<std::uint8_t>(static_cast<int>(PUSH1) + k - 1));
                code.insert(
                    code.end(), tail, static_cast<std::uint8_t>(JUMPDEST));
                auto const ref = reference_jumpdests(code);
                Intercode const ic{code.data(), code.size()};
                for (std::size_t i = 0; i < code.size(); ++i) {
                    ASSERT_EQ(ic.is_jumpdest(i), ref[i])
                        << "size=" << code.size() << " pc=" << i;
                }
                ASSERT_FALSE(ic.is_jumpdest(code.size()));
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
                    std::vector<std::uint8_t> code(
                        prefix, static_cast<std::uint8_t>(JUMPDEST));
                    code.push_back(static_cast<std::uint8_t>(
                        static_cast<int>(PUSH1) + k1 - 1));
                    code.insert(
                        code.end(),
                        static_cast<std::size_t>(gap),
                        static_cast<std::uint8_t>(JUMPDEST));
                    code.push_back(static_cast<std::uint8_t>(
                        static_cast<int>(PUSH1) + k2 - 1));
                    code.insert(
                        code.end(), 36, static_cast<std::uint8_t>(JUMPDEST));
                    auto const ref = reference_jumpdests(code);
                    Intercode const ic{code.data(), code.size()};
                    for (std::size_t i = 0; i < code.size(); ++i) {
                        ASSERT_EQ(ic.is_jumpdest(i), ref[i])
                            << "size=" << code.size() << " pc=" << i;
                    }
                    ASSERT_FALSE(ic.is_jumpdest(code.size()));
                }
            }
        }
    }
}

TEST(Intercode, JumpdestScanUniform)
{
    static constexpr std::uint8_t fills[] = {
        static_cast<std::uint8_t>(JUMPDEST),
        static_cast<std::uint8_t>(PUSH1),
        static_cast<std::uint8_t>(PUSH32),
        static_cast<std::uint8_t>(STOP),
        0xff,
        static_cast<std::uint8_t>(PUSH1) - 1};
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
                c = static_cast<std::uint8_t>(
                    static_cast<int>(PUSH1) + (rng() % 32));
            }
            else if (r < push_pct + jd_pct) {
                c = static_cast<std::uint8_t>(JUMPDEST);
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
    }
}

TEST(Intercode, JumpdestScanLargeAndBoundaries)
{
    // Large inputs exercise the many-block cross-128-bit-lane entry carry, and
    // sizes straddling 32-byte block boundaries exercise the kernel's tail.
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
        // Worst case: random JUMPDEST/ADD, both one byte, so the scan visits
        // every byte and the PUSH/JUMPDEST branches mispredict maximally.
        std::vector<std::uint8_t> worst(n);
        for (auto &c : worst) {
            c = (rng() & 1) ? static_cast<std::uint8_t>(JUMPDEST)
                            : static_cast<std::uint8_t>(ADD);
        }
        auto const worst_ref = reference_jumpdests(worst);
        Intercode const worst_ic{worst.data(), worst.size()};
        for (std::size_t i = 0; i < worst.size(); ++i) {
            ASSERT_EQ(worst_ic.is_jumpdest(i), worst_ref[i])
                << "worst size=" << n << " pc=" << i;
        }
        ASSERT_FALSE(worst_ic.is_jumpdest(n));

        // A PUSH-heavy program: immediates that may hide 0x5b bytes, with
        // boundaries at every alignment across many blocks.
        std::vector<std::uint8_t> pushy(n);
        for (auto &c : pushy) {
            int const r = static_cast<int>(rng() % 100);
            if (r < 55) {
                c = static_cast<std::uint8_t>(
                    static_cast<int>(PUSH1) + (rng() % 32));
            }
            else if (r < 75) {
                c = static_cast<std::uint8_t>(JUMPDEST);
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
    }
}

#if defined(__AVX2__)
// The AVX2 scan (what x86 validators run) and the scalar scan (the non-AVX2
// path, compiled for the RISC-V zkVM guest) both feed a consensus-relevant
// map, so they must produce identical bits. Only an AVX2 build compiles both;
// elsewhere CI compiles just one, so this is where the two are pinned equal.
TEST(Intercode, ScalarAndSimdScansAgree)
{
    std::mt19937_64 rng(0xD1FF);
    for (int t = 0; t < 6000; ++t) {
        std::size_t const n = rng() % 4096;
        std::vector<std::uint8_t> code(n + 33, 0); // trailing padding for AVX2
        int const push_pct = static_cast<int>(rng() % 60);
        int const jd_pct = static_cast<int>(rng() % 40);
        for (std::size_t i = 0; i < n; ++i) {
            int const r = static_cast<int>(rng() % 100);
            if (r < push_pct) {
                code[i] = static_cast<std::uint8_t>(
                    static_cast<int>(PUSH1) + (rng() % 32));
            }
            else if (r < push_pct + jd_pct) {
                code[i] = static_cast<std::uint8_t>(JUMPDEST);
            }
            else {
                code[i] = static_cast<std::uint8_t>(rng());
            }
        }
        std::vector<std::uint64_t> scalar_bits(
            detail::jumpdest_word_count(n), 0);
        std::vector<std::uint64_t> simd_bits(detail::jumpdest_word_count(n), 0);
        detail::find_jumpdests_scalar(code.data(), n, scalar_bits.data());
        detail::find_jumpdests_avx2(code.data(), n, simd_bits.data());
        ASSERT_EQ(scalar_bits, simd_bits) << "t=" << t << " size=" << n;
    }

    // Every size across the first few blocks, with a deterministic opcode mix,
    // to pin the tail and the cross-128-bit-lane entry carry.
    for (std::size_t n = 0; n <= 160; ++n) {
        std::vector<std::uint8_t> code(n + 33, 0);
        for (std::size_t i = 0; i < n; ++i) {
            code[i] = static_cast<std::uint8_t>((i * 7 + 3) & 0xff);
        }
        std::vector<std::uint64_t> scalar_bits(
            detail::jumpdest_word_count(n), 0);
        std::vector<std::uint64_t> simd_bits(detail::jumpdest_word_count(n), 0);
        detail::find_jumpdests_scalar(code.data(), n, scalar_bits.data());
        detail::find_jumpdests_avx2(code.data(), n, simd_bits.data());
        ASSERT_EQ(scalar_bits, simd_bits) << "size=" << n;
    }
}
#endif
