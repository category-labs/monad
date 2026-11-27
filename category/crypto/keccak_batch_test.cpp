// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT
#include <category/crypto/keccak.h>
#include <category/crypto/keccak_batch.h>

#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <random>
#include <vector>

namespace
{
    using Digest = std::array<uint8_t, 32>;
    using BatchFn = void (*)(monad_keccak256_job const *, size_t);

    constexpr size_t max_len = 700; // spans six 136-byte blocks
    constexpr size_t max_count = 17; // two 8-lane groups and a remainder

    bool avx512_supported()
    {
        return __builtin_cpu_supports("avx512f") &&
               __builtin_cpu_supports("avx512vl");
    }

    std::vector<uint8_t> random_bytes(size_t const n)
    {
        std::mt19937_64 rng{n};
        std::vector<uint8_t> bytes(n);
        for (auto &b : bytes) {
            b = static_cast<uint8_t>(rng());
        }
        return bytes;
    }

    Digest single(uint8_t const *const in, size_t const len)
    {
        Digest d;
        monad_keccak256(in, len, d.data());
        return d;
    }

    void
    expect_matches_single(BatchFn const fn, std::vector<size_t> const &lens)
    {
        auto const data = random_bytes(lens.size() * max_len);
        std::vector<Digest> got(lens.size());
        std::vector<monad_keccak256_job> jobs;
        jobs.reserve(lens.size());
        for (size_t i = 0; i < lens.size(); ++i) {
            jobs.push_back(
                {.in = data.data() + i * max_len,
                 .len = lens[i],
                 .out = got[i].data()});
        }
        fn(jobs.data(), jobs.size());
        for (size_t i = 0; i < jobs.size(); ++i) {
            EXPECT_EQ(got[i], single(jobs[i].in, jobs[i].len))
                << "job " << i << " of " << jobs.size() << ", len " << lens[i];
        }
    }

    void expect_every_length_in_every_lane(BatchFn const fn)
    {
        for (size_t base = 0; base <= max_len; ++base) {
            std::vector<size_t> lens(8);
            for (size_t i = 0; i < lens.size(); ++i) {
                lens[i] = (base + 37 * i) % (max_len + 1);
            }
            expect_matches_single(fn, lens);
        }
    }

    void expect_every_count(BatchFn const fn)
    {
        for (size_t count = 0; count <= max_count; ++count) {
            expect_matches_single(fn, std::vector<size_t>(count, 32));
            std::vector<size_t> mixed(count);
            for (size_t i = 0; i < count; ++i) {
                mixed[i] = (i * 61) % (max_len + 1);
            }
            expect_matches_single(fn, mixed);
        }
    }

    void expect_in_place(BatchFn const fn)
    {
        for (size_t count = 1; count <= max_count; ++count) {
            auto data = random_bytes(count * max_len);
            std::vector<monad_keccak256_job> jobs;
            std::vector<Digest> want;
            jobs.reserve(count);
            want.reserve(count);
            for (size_t i = 0; i < count; ++i) {
                uint8_t *const buf = data.data() + i * max_len;
                size_t const len =
                    std::array<size_t, 5>{0, 20, 32, 200, 300}[i % 5];
                want.push_back(single(buf, len));
                jobs.push_back({.in = buf, .len = len, .out = buf});
            }
            fn(jobs.data(), jobs.size());
            for (size_t i = 0; i < count; ++i) {
                Digest got;
                std::copy_n(jobs[i].out, got.size(), got.begin());
                EXPECT_EQ(got, want[i]) << "job " << i << " of " << count;
            }
        }
    }

    void expect_correct(BatchFn const fn)
    {
        expect_every_length_in_every_lane(fn);
        expect_every_count(fn);
        expect_in_place(fn);
    }
}

TEST(KeccakBatch, avx2_matches_single)
{
    expect_correct(monad_keccak256_batch_avx2);
}

TEST(KeccakBatch, avx512_matches_single)
{
    if (!avx512_supported()) {
        GTEST_SKIP() << "CPU lacks AVX-512F/VL";
    }
    expect_correct(monad_keccak256_batch_avx512);
}

TEST(KeccakBatch, dispatch_matches_single)
{
    expect_correct(monad_keccak256_batch);
}

TEST(KeccakBatch, empty_message_known_answer)
{
    Digest got;
    monad_keccak256_job const job{.in = nullptr, .len = 0, .out = got.data()};
    monad_keccak256_batch(&job, 1);
    EXPECT_EQ(got, (Digest{0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
                           0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
                           0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
                           0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70}));
}
