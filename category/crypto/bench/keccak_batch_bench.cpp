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

// Throughput of monad_keccak256_batch() kernels against one
// monad_keccak256() call per message. Pin to one core for stable numbers.

#include <category/crypto/keccak.h>
#include <category/crypto/keccak_batch.h>

#include <algorithm>
#include <array>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <random>
#include <ratio>
#include <string>
#include <utility>
#include <vector>

namespace
{
    constexpr size_t message_count = 1024;
    constexpr size_t message_stride = 640; // >= longest workload message

    struct Workload
    {
        std::string name;
        std::vector<size_t> lens;
    };

    std::vector<Workload> make_workloads()
    {
        std::vector<Workload> workloads;
        for (size_t const len : std::array<size_t, 5>{20, 32, 100, 200, 532}) {
            workloads.push_back(
                {std::to_string(len), std::vector(message_count, len)});
        }
        std::mt19937_64 rng{99};
        std::uniform_int_distribution<size_t> dist{20, 532};
        std::vector<size_t> mixed(message_count);
        for (auto &len : mixed) {
            len = dist(rng);
        }
        workloads.push_back({"20-532", mixed});
        std::ranges::sort(mixed);
        workloads.push_back({"20-532 sorted", std::move(mixed)});
        return workloads;
    }

    // Best of several trials, in nanoseconds per message.
    double time_per_hash(std::function<void()> const &hash_all)
    {
        constexpr int trials = 25;
        constexpr int reps = 16;
        double best = 1e300;
        for (int t = 0; t < trials; ++t) {
            auto const start = std::chrono::steady_clock::now();
            for (int r = 0; r < reps; ++r) {
                hash_all();
            }
            std::chrono::duration<double, std::nano> const elapsed =
                std::chrono::steady_clock::now() - start;
            best = std::min(
                best,
                elapsed.count() / (reps * static_cast<double>(message_count)));
        }
        return best;
    }
}

int main()
{
    bool const avx512 =
        __builtin_cpu_supports("avx512f") && __builtin_cpu_supports("avx512vl");

    std::vector<uint8_t> data(message_count * message_stride);
    std::mt19937_64 rng{42};
    for (auto &b : data) {
        b = static_cast<uint8_t>(rng());
    }
    std::vector<uint8_t> digests(message_count * 32);
    std::vector<monad_keccak256_job> jobs(message_count);
    auto const set_lengths = [&](std::vector<size_t> const &lens) {
        for (size_t i = 0; i < message_count; ++i) {
            jobs[i] = {
                .in = data.data() + i * message_stride,
                .len = lens[i],
                .out = digests.data() + i * 32};
        }
    };

    auto const hash_single = [&] {
        for (auto const &job : jobs) {
            monad_keccak256(job.in, job.len, job.out);
        }
    };

    set_lengths(std::vector<size_t>(message_count, 32));
    auto const warm_until =
        std::chrono::steady_clock::now() + std::chrono::seconds(2);
    while (std::chrono::steady_clock::now() < warm_until) {
        hash_single();
    }

    std::printf(
        "%-14s %10s %10s %10s   ns per message, best of 25\n",
        "bytes",
        "single",
        "avx2",
        "avx512");
    for (auto const &w : make_workloads()) {
        set_lengths(w.lens);
        double const single = time_per_hash(hash_single);
        double const avx2 = time_per_hash(
            [&] { monad_keccak256_batch_avx2(jobs.data(), jobs.size()); });
        double const wide = avx512 ? time_per_hash([&] {
            monad_keccak256_batch_avx512(jobs.data(), jobs.size());
        })
                                   : 0.0;
        std::printf(
            "%-14s %10.1f %10.1f %10.1f   avx2 %.2fx, avx512 %.2fx\n",
            w.name.c_str(),
            single,
            avx2,
            wide,
            single / avx2,
            avx512 ? single / wide : 0.0);
    }
    return 0;
}
