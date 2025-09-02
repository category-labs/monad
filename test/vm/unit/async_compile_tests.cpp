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

#include <category/vm/code.hpp>
#include <category/vm/compiler.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <thread>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::compiler;

namespace
{
    std::vector<uint8_t> test_code(uint64_t index)
    {
        std::vector<uint8_t> code = {PUSH1, 1, PUSH8};
        for (uint64_t i = 0; i < 8; ++i) {
            code.push_back(static_cast<uint8_t>(index >> 8 * (7 - i)));
        }
        code.push_back(RETURN);
        return code;
    }

    evmc::bytes32 test_hash(uint64_t index)
    {
        evmc::bytes32 h{};
        for (uint64_t i = 0; i < 8; ++i) {
            h.bytes[31 - i] = static_cast<uint8_t>(index >> 8 * (7 - i));
        }
        return h;
    }
}

TEST(async_compile_test, stress)
{
    using traits = EvmTraits<EVMC_CANCUN>;

    constexpr size_t P = 10;
    constexpr size_t L = 120;
    constexpr size_t N = L * 12;

    Compiler compiler{true, L};

    auto first_start_time = std::chrono::steady_clock::now();
    compiler.compile<traits>(make_shared_intercode(test_code(2 * N)));
    auto first_end_time = std::chrono::steady_clock::now();
    auto compile_time_estimate = first_end_time - first_start_time;

    auto producer = [&](uint64_t start_index) {
        std::unordered_set<uint64_t> producer_set;
        // Spam async compiler with `L` async compilation requests followed
        // by a sleep period to let the compiler partially empty the queue.
        for (uint64_t i = 0; i < N;) {
            uint64_t const c = std::min(i + L, N);
            for (; i < c; ++i) {
                uint64_t const index = start_index + i;
                auto code = test_code(index);
                auto hash = test_hash(index);
                auto icode = make_shared_intercode(std::move(code));
                if (compiler.async_compile<traits>(hash, icode)) {
                    auto [_, inserted] = producer_set.insert(index);
                    ASSERT_TRUE(inserted);
                }
            }
            std::this_thread::sleep_for(compile_time_estimate * L / 4);
        }

        compiler.debug_wait_for_empty_queue();

        for (uint64_t const index : producer_set) {
            auto vcode = compiler.find_varcode(test_hash(index));
            ASSERT_TRUE(vcode.has_value());
            auto ncode = (*vcode)->nativecode();
            ASSERT_TRUE(!!ncode);

            auto entry = ncode->entrypoint();
            ASSERT_TRUE(entry != nullptr);

            auto ctx = runtime::Context::empty();
            ctx.gas_remaining = 100;
            entry(&ctx, nullptr);

            auto const &ret = ctx.result;
            ASSERT_EQ(ret.status, runtime::StatusCode::Success);
            ASSERT_EQ(uint256_t::load_le(ret.offset), index);
            ASSERT_EQ(uint256_t::load_le(ret.size), 1);
        }
    };

    std::vector<std::thread> producers;
    for (size_t i = 0; i < P; ++i) {
        producers.emplace_back(producer, (i * N) / 2);
    }
    for (size_t i = 0; i < P; ++i) {
        producers[i].join();
    }
}

TEST(async_compile_test, disable)
{
    Compiler compiler{false};

    for (auto i = 0u; i < 32; ++i) {
        auto const code = test_code(i);
        auto const hash = test_hash(i);
        auto const icode = make_shared_intercode(std::move(code));

        ASSERT_TRUE(
            compiler.async_compile<EvmTraits<EVMC_PRAGUE>>(hash, icode));
    }

    compiler.debug_wait_for_empty_queue();

    for (auto i = 0u; i < 32; ++i) {
        auto const vcode = compiler.find_varcode(test_hash(i));
        ASSERT_TRUE(vcode.has_value());
        auto const ncode = (*vcode)->nativecode();
        ASSERT_TRUE(!!ncode);

        auto const entry = ncode->entrypoint();
        ASSERT_TRUE(entry == nullptr);
    }
}
