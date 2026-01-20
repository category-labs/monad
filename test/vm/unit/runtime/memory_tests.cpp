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

#include "fixture.hpp"

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/types.hpp>

#include <algorithm>
#include <cstdint>
#include <generator>

using namespace monad;
using namespace monad::vm::runtime;
using namespace monad::vm::compiler::test;

namespace
{
    template <Traits traits>
    class MemoryTestMachine
    {
        vm::test::TestMemory init_memory_;
        Context *prev_rt_ctx_;
        evmc::MockedHost &host_;

    public:
        MemoryTestMachine(evmc::MockedHost &host)
            : prev_rt_ctx_{}
            , host_{host}
        {
        }

        void call(std::function<void(Context &)> continuation)
        {
            evmc_message msg{};
            if (prev_rt_ctx_) {
                auto const &m = prev_rt_ctx_->memory;
                msg.memory = m.data + m.size;
                msg.memory_handle = m.data_handle;
                msg.memory_capacity = m.capacity - m.size;
                MONAD_VM_ASSERT(m.size <= m.capacity);
            }
            else {
                // init_memory = std::make_optional<vm::test::TestMemory>();
                msg.memory_handle = init_memory_.data;
                msg.memory = init_memory_.data;
                msg.memory_capacity = init_memory_.capacity;
            }

            Context rt_ctx = Context::from(
                &host_.get_interface(), host_.to_context(), &msg, {});
            rt_ctx.gas_remaining = 100'000'000;

            auto const tmp_rt_ctx = prev_rt_ctx_;
            prev_rt_ctx_ = &rt_ctx;

            continuation(rt_ctx);

            prev_rt_ctx_ = tmp_rt_ctx;

            rt_ctx.return_to<traits>(prev_rt_ctx_);
        }
    };

    struct MemoryTestMachineConfig
    {
        uint8_t depth;
        std::vector<std::pair<uint8_t, bool>> pre_calls;
        std::vector<std::pair<uint8_t, bool>> post_calls;
    };

    template <Traits traits>
    void increase_capacity(Context &ctx)
    {
        auto const capacity_before = ctx.memory.capacity;
        ctx.expand_memory<traits>(
            Bin<29>::unsafe_from(ctx.memory.capacity + 1));
        auto const capacity_after = ctx.memory.capacity;
        auto const parent_total_size = *ctx.memory.parent_total_size();
        ASSERT_EQ(
            capacity_after,
            2 * (parent_total_size + capacity_before + 32) - parent_total_size);
    }

    void set_memory(Context &ctx, uint8_t depth, bool full)
    {
        if (full) {
            ctx.memory.size = ctx.memory.capacity;
        }
        else if (ctx.memory.capacity) {
            ctx.memory.size =
                std::max(ctx.memory.capacity - 32, ctx.memory.size);
        }
        std::memset(ctx.memory.data, depth, ctx.memory.size);
    }

    void invariant_check(Context &ctx, uint8_t depth)
    {
        uint8_t const *const data_handle = ctx.memory.data_handle;
        uint8_t const *const data = ctx.memory.data;
        uint32_t const size = ctx.memory.size;
        uint8_t d = data_handle[0];
        for (uint8_t const *p = data_handle; p < data; ++p) {
            ASSERT_GE(d, *p);
            ASSERT_GT(*p, depth);
            d = *p;
        }
        for (uint8_t const *p = data; p < data + size; ++p) {
            ASSERT_EQ(*p, depth);
        }
        for (uint8_t const *p = data + size; p < data + ctx.memory.capacity;
             ++p) {
            MONAD_VM_ASSERT(*p == 0);
            ASSERT_EQ(*p, 0);
        }
    }

    template <Traits traits>
    void memory_test_machine_config_call(
        Context &ctx, MemoryTestMachine<traits> &machine,
        MemoryTestMachineConfig config)
    {
        MONAD_VM_ASSERT(config.pre_calls.size() == config.depth);
        MONAD_VM_ASSERT(config.post_calls.size() == config.depth);
        if (config.depth == 0) {
            return;
        }

        uint8_t const depth = config.depth;
        config.depth -= 1;

        auto const [n_pre, full_pre] = config.pre_calls.back();
        config.pre_calls.pop_back();
        MONAD_VM_ASSERT(n_pre <= 2);

        auto const [n_post, full_post] = config.post_calls.back();
        config.post_calls.pop_back();
        MONAD_VM_ASSERT(n_post <= 2);

        for (uint8_t i = 0; i < n_pre; ++i) {
            increase_capacity<traits>(ctx);
        }
        set_memory(ctx, depth, full_pre);

        invariant_check(ctx, depth);

        machine.call([&](auto &next_ctx) {
            memory_test_machine_config_call(next_ctx, machine, config);
        });

        invariant_check(ctx, depth);

        for (uint8_t i = 0; i < n_post; ++i) {
            increase_capacity<traits>(ctx);
        }
        set_memory(ctx, depth, full_post);

        invariant_check(ctx, depth);
    }

    template <Traits traits>
    void run_memory_test_machine(
        evmc::MockedHost &host, MemoryTestMachineConfig config)
    {
        MemoryTestMachine<traits> machine{host};
        machine.call([&](auto &ctx) {
            memory_test_machine_config_call(ctx, machine, config);
        });
    }

    std::generator<MemoryTestMachineConfig const &>
    memory_test_machine_configs()
    {
        std::vector<std::tuple<uint8_t, bool, uint8_t, bool>> combos;
        for (uint8_t n_pre = 0; n_pre <= 2; ++n_pre) {
            for (uint8_t full_pre = 0; full_pre <= 1; ++full_pre) {
                for (uint8_t n_post = 0; n_post <= 2; ++n_post) {
                    for (uint8_t full_post = 0; full_post <= 1; ++full_post) {
                        combos.emplace_back(n_pre, full_pre, n_post, full_post);
                    }
                }
            }
        }

        MemoryTestMachineConfig config{
            .depth = 0, .pre_calls = {}, .post_calls = {}};

        co_yield config;

        config.depth = 1;
        config.pre_calls.resize(config.depth);
        config.post_calls.resize(config.depth);
        for (auto [n, b, m, c] : combos) {
            config.pre_calls[0] = {n, b};
            config.post_calls[0] = {m, c};
            co_yield config;
        }

        config.depth = 2;
        config.pre_calls.resize(config.depth);
        config.post_calls.resize(config.depth);
        for (auto [n0, b0, m0, c0] : combos) {
            config.pre_calls[0] = {n0, b0};
            config.post_calls[0] = {m0, c0};
            for (auto [n1, b1, m1, c1] : combos) {
                config.pre_calls[1] = {n1, b1};
                config.post_calls[1] = {m1, c1};
                co_yield config;
            }
        }
    }
}

TEST_F(RuntimeTest, EmptyMemory)
{
    ASSERT_EQ(ctx_.memory.size, 0);
    ASSERT_EQ(ctx_.memory.cost, 0);
}

TYPED_TEST(RuntimeTraitsTest, MStore)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();

    switch (memory_version) {
    case Memory::Version::V1:
        this->ctx_.gas_remaining = 6;
        break;
    case Memory::Version::MIP3:
        this->ctx_.gas_remaining = 1;
        break;
    }

    TestFixture::call(mstore<traits>, 0, 0xFF);
    ASSERT_EQ(this->ctx_.memory.size, 32);
    ASSERT_EQ(this->ctx_.memory.data[31], 0xFF);
    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.gas_remaining, 3);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.gas_remaining, 1);
        break;
    }

    TestFixture::call(mstore<traits>, 1, 0xFF);
    ASSERT_EQ(this->ctx_.memory.size, 64);
    ASSERT_EQ(this->ctx_.memory.data[31], 0x00);
    ASSERT_EQ(this->ctx_.memory.data[32], 0xFF);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 6);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 1);
        break;
    }
}

TYPED_TEST(RuntimeTraitsTest, MStoreWord)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();

    switch (memory_version) {
    case Memory::Version::V1:
        this->ctx_.gas_remaining = 3;
        break;
    case Memory::Version::MIP3:
        this->ctx_.gas_remaining = 0;
        break;
    }

    TestFixture::call(
        mstore<traits>,
        0,
        0x000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F_u256);

    ASSERT_EQ(this->ctx_.memory.size, 32);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 3);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 0);
        break;
    }

    for (auto i = 0u; i < 31; ++i) {
        ASSERT_EQ(this->ctx_.memory.data[i], i);
    }
}

TYPED_TEST(RuntimeTraitsTest, MCopy)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();

    switch (memory_version) {
    case Memory::Version::V1:
        this->ctx_.gas_remaining = 20;
        break;
    case Memory::Version::MIP3:
        this->ctx_.gas_remaining = 15;
        break;
    }

    TestFixture::call(mstore8<traits>, 1, 1);
    TestFixture::call(mstore8<traits>, 2, 2);
    TestFixture::call(mcopy<traits>, 3, 1, 33);

    ASSERT_EQ(this->ctx_.gas_remaining, 8);
    ASSERT_EQ(this->ctx_.memory.size, 64);
    ASSERT_EQ(this->ctx_.memory.data[0], 0);
    ASSERT_EQ(this->ctx_.memory.data[1], 1);
    ASSERT_EQ(this->ctx_.memory.data[2], 2);
    ASSERT_EQ(this->ctx_.memory.data[3], 1);
    ASSERT_EQ(this->ctx_.memory.data[4], 2);
    ASSERT_EQ(this->ctx_.memory.data[5], 0);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 6);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 1);
        break;
    }
}

TYPED_TEST(RuntimeTraitsTest, MStore8)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();

    switch (memory_version) {
    case Memory::Version::V1:
        this->ctx_.gas_remaining = 3;
        break;
    case Memory::Version::MIP3:
        this->ctx_.gas_remaining = 0;
        break;
    }

    TestFixture::call(mstore8<traits>, 0, 0xFFFF);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);
    ASSERT_EQ(this->ctx_.memory.data[0], 0xFF);
    ASSERT_EQ(this->ctx_.memory.data[1], 0x00);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 3);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 0);
        break;
    }

    TestFixture::call(mstore8<traits>, 1, 0xFF);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);
    ASSERT_EQ(this->ctx_.memory.data[0], 0xFF);
    ASSERT_EQ(this->ctx_.memory.data[1], 0xFF);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 3);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 0);
        break;
    }

    ASSERT_EQ(
        TestFixture::call(mload<traits>, 0),
        0xFFFF000000000000000000000000000000000000000000000000000000000000_u256);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 3);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 0);
        break;
    }
}

TYPED_TEST(RuntimeTraitsTest, MLoad)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();

    switch (memory_version) {
    case Memory::Version::V1:
        this->ctx_.gas_remaining = 6;
        break;
    case Memory::Version::MIP3:
        this->ctx_.gas_remaining = 1;
        break;
    }

    TestFixture::call(mstore<traits>, 0, 0xFF);
    ASSERT_EQ(TestFixture::call(mload<traits>, 0), 0xFF);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.gas_remaining, 3);
        ASSERT_EQ(this->ctx_.memory.cost, 3);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.gas_remaining, 1);
        ASSERT_EQ(this->ctx_.memory.cost, 0);
        break;
    }

    ASSERT_EQ(TestFixture::call(mload<traits>, 1), 0xFF00);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 6);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 1);
        break;
    }
}

TYPED_TEST(RuntimeTraitsTest, QuadraticCosts)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();

    switch (memory_version) {
    case Memory::Version::V1:
        this->ctx_.gas_remaining = 101;
        break;
    case Memory::Version::MIP3:
        this->ctx_.gas_remaining = 16;
        break;
    }

    ASSERT_EQ(TestFixture::call(mload<traits>, 1024), 0);
    ASSERT_EQ(this->ctx_.gas_remaining, 0);
    ASSERT_EQ(this->ctx_.memory.size, 1056);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(this->ctx_.memory.cost, 101);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(this->ctx_.memory.cost, 16);
        break;
    }
}

template <Memory::Version memory_version>
void test_expand_memory_impl(Context &ctx, std::function<void(Bin<29>)> expand)
{
    ctx.gas_remaining = 1'000'000;

    ASSERT_EQ(ctx.memory.capacity, vm::test::TestMemory::capacity);

    uint32_t const new_capacity = (vm::test::TestMemory::capacity + 32) * 2;

    expand(Bin<29>::unsafe_from(vm::test::TestMemory::capacity + 1));
    ASSERT_EQ(ctx.memory.size, vm::test::TestMemory::capacity + 32);
    ASSERT_EQ(ctx.memory.capacity, new_capacity);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(ctx.memory.cost, 419);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(ctx.memory.cost, 64);
        break;
    }

    ASSERT_TRUE(std::all_of(
        ctx.memory.data, ctx.memory.data + ctx.memory.size, [](auto b) {
            return b == 0;
        }));

    expand(Bin<29>::unsafe_from(vm::test::TestMemory::capacity + 90));
    ASSERT_EQ(ctx.memory.size, vm::test::TestMemory::capacity + 96);
    ASSERT_EQ(ctx.memory.capacity, new_capacity);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(ctx.memory.cost, 426);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(ctx.memory.cost, 65);
        break;
    }

    ASSERT_TRUE(std::all_of(
        ctx.memory.data, ctx.memory.data + ctx.memory.size, [](auto b) {
            return b == 0;
        }));

    expand(Bin<29>::unsafe_from(new_capacity));
    ASSERT_EQ(ctx.memory.size, new_capacity);
    ASSERT_EQ(ctx.memory.capacity, new_capacity);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(ctx.memory.cost, 904);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(ctx.memory.cost, 129);
        break;
    }

    ASSERT_TRUE(std::all_of(
        ctx.memory.data, ctx.memory.data + ctx.memory.size, [](auto b) {
            return b == 0;
        }));

    expand(Bin<29>::unsafe_from(vm::test::TestMemory::capacity * 4 + 1));
    ASSERT_EQ(ctx.memory.size, vm::test::TestMemory::capacity * 4 + 32);
    ASSERT_EQ(
        ctx.memory.capacity, (vm::test::TestMemory::capacity * 4 + 32) * 2);

    switch (memory_version) {
    case Memory::Version::V1:
        ASSERT_EQ(ctx.memory.cost, 2053);
        break;
    case Memory::Version::MIP3:
        ASSERT_EQ(ctx.memory.cost, 256);
        break;
    }

    ASSERT_TRUE(std::all_of(
        ctx.memory.data, ctx.memory.data + ctx.memory.size, [](auto b) {
            return b == 0;
        }));

    if (memory_version == Memory::Version::MIP3) {
        constexpr uint32_t max_size = 8 * 1024 * 1024;
        monad_vm_runtime_increase_memory_mip3(
            Bin<29>::unsafe_from(max_size - 1), &ctx);
        ASSERT_EQ(ctx.memory.capacity, max_size * 2);
        ASSERT_EQ(ctx.memory.cost, max_size / 64);
        ASSERT_TRUE(std::all_of(
            ctx.memory.data, ctx.memory.data + ctx.memory.size, [](auto b) {
                return b == 0;
            }));
    }
}

TYPED_TEST(RuntimeTraitsTest, ExpandMemory)
{
    using traits = TestFixture::Trait;
    constexpr auto memory_version = TestFixture::get_memory_version();
    test_expand_memory_impl<memory_version>(
        this->ctx_, [this](Bin<29> const s) {
            this->ctx_.template expand_memory<traits>(s);
        });
}

TEST_F(RuntimeTest, RuntimeIncreaseMemoryV1)
{
    constexpr auto memory_version = Memory::Version::V1;
    test_expand_memory_impl<memory_version>(
        this->ctx_, [this](Bin<29> const s) {
            monad_vm_runtime_increase_memory_v1(s, &ctx_);
        });
}

TEST_F(RuntimeTest, RuntimeIncreaseMemoryMIP3)
{
    constexpr auto memory_version = Memory::Version::MIP3;
    test_expand_memory_impl<memory_version>(
        this->ctx_, [this](Bin<29> const s) {
            monad_vm_runtime_increase_memory_mip3(s, &ctx_);
        });
}

TEST_F(RuntimeTest, MemoryTestMachineV1)
{
    using traits = MonadTraits<MONAD_EIGHT>;
    for (auto const &config : memory_test_machine_configs()) {
        run_memory_test_machine<traits>(RuntimeTestBase::host_, config);
    }
}

TEST_F(RuntimeTest, MemoryTestMachineMIP3)
{
    using traits = MonadTraits<MONAD_NEXT>;
    for (auto const &config : memory_test_machine_configs()) {
        run_memory_test_machine<traits>(RuntimeTestBase::host_, config);
    }
}
