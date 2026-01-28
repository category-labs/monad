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
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/host.hpp>
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/varcode_cache.hpp>
#include <category/vm/vm.hpp>

#include <test/vm/utils/test_context.hpp>
#include <test/vm/utils/test_message.hpp>

#include <asmjit/core/jitruntime.h>

#include <ethash/keccak.hpp>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::compiler;

namespace
{
    std::pair<std::vector<uint8_t>, evmc::bytes32> make_bytecode(uint32_t bytes)
    {
        std::vector<uint8_t> bytecode{
            PUSH1,
            0,
            PUSH4,
            static_cast<uint8_t>(bytes >> 24),
            static_cast<uint8_t>(bytes >> 16),
            static_cast<uint8_t>(bytes >> 8),
            static_cast<uint8_t>(bytes),
            RETURN};
        auto hash = std::bit_cast<evmc::bytes32>(
            ethash::keccak256(bytecode.data(), bytecode.size()));
        return {bytecode, hash};
    }

    std::pair<std::vector<uint8_t>, evmc::bytes32>
    make_bytecode_with_compilation_failure()
    {
        std::vector<uint8_t> bytecode{PUSH4, 0, 0, 0, 0, JUMP, JUMPDEST};
        for (size_t i = 0; i < 150; ++i) {
            bytecode.push_back(JUMPI);
        }
        bytecode.push_back(JUMPDEST);
        auto dest = bytecode.size() - 1;
        bytecode[1] = static_cast<uint8_t>(dest >> 24);
        bytecode[2] = static_cast<uint8_t>(dest >> 16);
        bytecode[3] = static_cast<uint8_t>(dest >> 8);
        bytecode[4] = static_cast<uint8_t>(dest);
        auto hash = std::bit_cast<evmc::bytes32>(
            ethash::keccak256(bytecode.data(), bytecode.size()));
        return {bytecode, hash};
    }

    class HostMock : public Host
    {
        size_t calls_before_exception_;
        std::function<evmc::Result(Host &, evmc_message const &)> call_impl_;
        evmc_tx_context tx_context_{};

    public:
        struct Exception
        {
            std::string message;
        };

        HostMock(
            size_t calls_before_exception,
            std::function<evmc::Result(Host &, evmc_message const &)> call_impl)
            : calls_before_exception_{calls_before_exception}
            , call_impl_{std::move(call_impl)}
        {
        }

        bool account_exists(evmc::address const &) const noexcept override
        {
            return false;
        }

        evmc::bytes32 get_storage(evmc::address const &, evmc::bytes32 const &)
            const noexcept override
        {
            return evmc::bytes32{};
        }

        evmc_storage_status set_storage(
            evmc::address const &, evmc::bytes32 const &,
            evmc::bytes32 const &) noexcept override
        {
            return evmc_storage_status{};
        }

        evmc::uint256be
        get_balance(evmc::address const &) const noexcept override
        {
            return evmc::uint256be{};
        }

        size_t get_code_size(evmc::address const &) const noexcept override
        {
            return 0;
        }

        evmc::bytes32
        get_code_hash(evmc::address const &) const noexcept override
        {
            return evmc::bytes32{};
        }

        size_t copy_code(evmc::address const &, size_t, uint8_t *, size_t)
            const noexcept override
        {
            return 0;
        }

        bool selfdestruct(
            evmc::address const &, evmc::address const &) noexcept override
        {
            return false;
        }

        evmc::Result call(evmc_message const &msg) noexcept override
        {
            try {
                if (calls_before_exception_-- == 0) {
                    throw Exception{"exception"};
                }
                return call_impl_(*this, msg);
            }
            catch (...) {
                capture_current_exception();
            }
            stack_unwind();
        }

        evmc_tx_context const *get_tx_context() const noexcept override
        {
            return &tx_context_;
        }

        evmc::bytes32 get_block_hash(int64_t) const noexcept override
        {
            return evmc::bytes32{};
        }

        void emit_log(
            evmc::address const &, uint8_t const *, size_t,
            evmc::bytes32 const *, size_t) noexcept override
        {
        }

        evmc_access_status
        access_account(evmc::address const &) noexcept override
        {
            return evmc_access_status{};
        }

        evmc_access_status access_storage(
            evmc::address const &, evmc::bytes32 const &) noexcept override
        {
            return evmc_access_status{};
        }

        evmc::bytes32 get_transient_storage(
            evmc::address const &,
            evmc::bytes32 const &) const noexcept override
        {
            return evmc::bytes32{};
        }

        void set_transient_storage(
            evmc::address const &, evmc::bytes32 const &,
            evmc::bytes32 const &) noexcept override
        {
        }
    };
}

TEST(MonadVmInterface, VarcodeCacheEmptyCode)
{
    static uint32_t const bytecode_cache_weight = 3;
    static uint32_t const warm_cache_kb = 2 * bytecode_cache_weight;
    static uint32_t const max_cache_kb = warm_cache_kb;

    VarcodeCache cache{max_cache_kb, warm_cache_kb};

    uint8_t *const p = nullptr;
    std::span<uint8_t const> empty_code{p, 0};
    auto code_hash = std::bit_cast<evmc::bytes32>(
        ethash::keccak256(empty_code.data(), empty_code.size()));

    auto vcode0 = cache.try_set(code_hash, make_shared_intercode(empty_code));

    ASSERT_EQ(vcode0, cache.get(code_hash));
    ASSERT_EQ(vcode0->intercode()->size(), 0);
    ASSERT_EQ(vcode0->nativecode(), nullptr);

    auto vcode1 = cache.try_set_raw(code_hash, empty_code);

    ASSERT_EQ(vcode0, vcode1);
}

TEST(MonadVmInterface, VarcodeCache)
{
    static uint32_t const bytecode_cache_weight = 3;
    static uint32_t const warm_cache_kb = 2 * bytecode_cache_weight;
    static uint32_t const max_cache_kb = warm_cache_kb;

    VarcodeCache cache{max_cache_kb, warm_cache_kb};
    auto [bytecode0, hash0] = make_bytecode(0);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(
            static_cast<uint32_t>(bytecode0.size())),
        bytecode_cache_weight);
    auto icode0 = make_shared_intercode(bytecode0);
    asmjit::JitRuntime asmjit_rt;
    auto ncode0 = std::make_shared<Nativecode>(
        asmjit_rt, EvmTraits<EVMC_HOMESTEAD>::id(), nullptr, std::monostate{});

    ASSERT_FALSE(cache.get(hash0).has_value());
    cache.set(hash0, icode0, ncode0);

    ASSERT_FALSE(cache.is_warm());

    auto vcode0 = cache.get(hash0);

    ASSERT_TRUE(vcode0.has_value());
    ASSERT_EQ(vcode0.value()->intercode(), icode0);
    ASSERT_EQ(vcode0.value()->nativecode(), ncode0);
    ASSERT_EQ(vcode0, cache.get(hash0));
    ASSERT_EQ(vcode0, cache.try_set_raw(hash0, bytecode0));

    auto [bytecode1, hash1] = make_bytecode(1);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(
            static_cast<uint32_t>(bytecode1.size())),
        bytecode_cache_weight);
    auto icode1 = make_shared_intercode(bytecode1);

    auto vcode1 = cache.try_set(hash1, icode1);

    ASSERT_TRUE(cache.is_warm());

    ASSERT_NE(vcode0.value(), vcode1);
    ASSERT_EQ(vcode1->intercode(), icode1);
    ASSERT_EQ(vcode1->nativecode(), nullptr);
    ASSERT_EQ(vcode1, cache.get(hash1).value());
    ASSERT_EQ(vcode0, cache.get(hash0).value());
    ASSERT_EQ(vcode1, cache.try_set_raw(hash1, bytecode1));

    auto [bytecode2, hash2] = make_bytecode(2);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(
            static_cast<uint32_t>(bytecode2.size())),
        bytecode_cache_weight);
    auto icode2 = make_shared_intercode(bytecode2);

    auto vcode2 = cache.try_set(hash2, icode2);

    ASSERT_TRUE(cache.is_warm());

    ASSERT_NE(vcode2, vcode0.value());
    ASSERT_NE(vcode2, vcode1);
    ASSERT_EQ(vcode2->intercode(), icode2);
    ASSERT_EQ(vcode2->nativecode(), nullptr);
    ASSERT_EQ(vcode2, cache.get(hash2).value());
    ASSERT_EQ(vcode1, cache.get(hash1).value());
    ASSERT_FALSE(cache.get(hash0).has_value());
    ASSERT_EQ(vcode2, cache.try_set_raw(hash2, bytecode2));

    auto [bytecode3, hash3] = make_bytecode(3);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(
            static_cast<uint32_t>(bytecode3.size())),
        bytecode_cache_weight);

    auto vcode3 = cache.try_set_raw(hash3, bytecode3);

    ASSERT_TRUE(cache.is_warm());

    ASSERT_NE(vcode3, vcode0.value());
    ASSERT_NE(vcode3, vcode1);
    ASSERT_NE(vcode3, vcode2);
    auto vcode3_span = vcode3->intercode()->code_span();
    ASSERT_TRUE(std::equal(
        std::begin(vcode3_span),
        std::end(vcode3_span),
        std::begin(bytecode3),
        std::end(bytecode3)));
    ASSERT_EQ(vcode3->nativecode(), nullptr);
    ASSERT_EQ(vcode3, cache.get(hash3).value());
    ASSERT_EQ(vcode2, cache.get(hash2).value());
    ASSERT_FALSE(cache.get(hash1).has_value()); // evicted
    ASSERT_FALSE(cache.get(hash0).has_value()); // still evicted
}

TEST(MonadVmInterface, compile)
{
    VM vm;

    auto [bytecode1, hash1] = make_bytecode(1);
    auto icode1 = make_shared_intercode(bytecode1);

    auto ncode1 = vm.compiler().compile<EvmTraits<EVMC_HOMESTEAD>>(icode1);
    auto entry1 = ncode1->entrypoint();
    ASSERT_NE(entry1, nullptr);

    test::TestContext ctx1;
    entry1(&*ctx1, nullptr);

    ASSERT_EQ(uint256_t::load_le(ctx1->result.size), 0);
    ASSERT_EQ(uint256_t::load_le(ctx1->result.offset), 1);

    ASSERT_FALSE(vm.find_varcode(hash1).has_value());
}

TEST(MonadVmInterface, cached_compile)
{
    VM vm;

    auto [bytecode1, hash1] = make_bytecode(1);
    auto icode1 = make_shared_intercode(bytecode1);

    auto ncode1 =
        vm.compiler().cached_compile<EvmTraits<EVMC_HOMESTEAD>>(hash1, icode1);
    auto entry1 = ncode1->entrypoint();
    ASSERT_NE(entry1, nullptr);

    test::TestContext ctx1;
    entry1(&*ctx1, nullptr);

    ASSERT_EQ(uint256_t::load_le(ctx1->result.size), 0);
    ASSERT_EQ(uint256_t::load_le(ctx1->result.offset), 1);

    auto vcode1 = vm.find_varcode(hash1);
    ASSERT_TRUE(vcode1.has_value());
    ASSERT_EQ(vcode1.value()->intercode(), icode1);
    ASSERT_EQ(vcode1.value()->nativecode(), ncode1);
}

TEST(MonadVmInterface, async_compile)
{
    for (bool enabled : {false, true}) {
        VM vm{enabled};

        auto [bytecode1, hash1] = make_bytecode(1);
        auto icode1 = make_shared_intercode(bytecode1);

        ASSERT_TRUE(vm.compiler().async_compile<EvmTraits<EVMC_HOMESTEAD>>(
            hash1, icode1));
        vm.compiler().debug_wait_for_empty_queue();

        auto vcode1 = vm.find_varcode(hash1);
        ASSERT_TRUE(vcode1.has_value());
        ASSERT_EQ(vcode1.value()->intercode(), icode1);
        ASSERT_NE(vcode1.value()->nativecode(), nullptr);

        auto entry1 = (*vcode1)->nativecode()->entrypoint();
        if (enabled) {
            ASSERT_NE(entry1, nullptr);
            test::TestContext ctx1;
            entry1(&*ctx1, nullptr);
            ASSERT_EQ(uint256_t::load_le(ctx1->result.size), 0);
            ASSERT_EQ(uint256_t::load_le(ctx1->result.offset), 1);
        }
        else {
            ASSERT_EQ(entry1, nullptr);
        }
    }
}

TEST(MonadVmInterface, try_insert_varcode)
{
    VM vm;
    auto [bytecode1, hash1] = make_bytecode(1);
    auto icode1 = make_shared_intercode(bytecode1);
    auto vcode1 = vm.try_insert_varcode(hash1, icode1);
    ASSERT_EQ(vcode1->intercode(), icode1);
    ASSERT_EQ(vcode1->nativecode(), nullptr);
    ASSERT_EQ(vm.try_insert_varcode(hash1, icode1), vcode1);
    ASSERT_EQ(vm.try_insert_varcode_raw(hash1, bytecode1), vcode1);
}

TEST(MonadVmInterface, execute_bytecode_raw)
{
    VM vm;
    evmc::MockedHost host;

    auto [bytecode0, hash0] = make_bytecode(0);

    test::TestMessage msg{};
    msg->gas = 10;

    auto rt_ctx = runtime::Context::from(
        &host.get_interface(),
        host.to_context(),
        &*msg,
        {bytecode0.data(), bytecode0.size()});
    auto result = vm.execute_bytecode_raw<EvmTraits<EVMC_HOMESTEAD>>(
        rt_ctx, {bytecode0.data(), bytecode0.size()});
    ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    ASSERT_EQ(result.output_size, 0);
    ASSERT_EQ(result.gas_left, 4);
}

TEST(MonadVmInterface, execute_intercode_raw)
{
    VM vm;
    evmc::MockedHost host;

    auto [bytecode0, hash0] = make_bytecode(0);
    auto icode0 = make_shared_intercode(bytecode0);

    test::TestMessage msg{};
    msg->gas = 10;

    auto rt_ctx = runtime::Context::from(
        &host.get_interface(),
        host.to_context(),
        &*msg,
        {bytecode0.data(), bytecode0.size()});
    auto result =
        vm.execute_intercode_raw<EvmTraits<EVMC_HOMESTEAD>>(rt_ctx, icode0);
    ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    ASSERT_EQ(result.output_size, 0);
    ASSERT_EQ(result.gas_left, 4);
}

TEST(MonadVmInterface, execute_native_entrypoint_raw)
{
    VM vm;
    evmc::MockedHost host;

    using traits = EvmTraits<EVMC_HOMESTEAD>;

    auto [bytecode0, hash0] = make_bytecode(0);
    auto icode0 = make_shared_intercode(bytecode0);
    auto ncode0 = vm.compiler().compile<traits>(icode0);
    auto entry0 = ncode0->entrypoint();
    ASSERT_NE(entry0, nullptr);

    test::TestMessage msg{};
    msg->gas = 10;

    auto rt_ctx = runtime::Context::from(
        &host.get_interface(),
        host.to_context(),
        &*msg,
        {bytecode0.data(), bytecode0.size()});
    auto result = vm.execute_native_entrypoint_raw<traits>(rt_ctx, entry0);
    ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    ASSERT_EQ(result.output_size, 0);
    ASSERT_EQ(result.gas_left, 4);
}

TEST(MonadVmInterface, execute_raw)
{
    VM vm;
    evmc::MockedHost host;

    test::TestMessage msg{};
    msg->gas = 100'000'000;

    static uint32_t const warm_kb_threshold = 1 << 10; // 1MB
    vm.compiler().set_varcode_cache_warm_kb_threshold(warm_kb_threshold);

    // First parameter is just to avoid explicitly using .template operator()
    // when the lambda gets called.
    auto execute_raw =
        [&]<Traits traits>(
            traits, evmc::bytes32 const &hash, SharedVarcode const &vcode) {
            auto const &icode = vcode->intercode();
            auto rt_ctx = runtime::Context::from(
                &host.get_interface(),
                host.to_context(),
                &*msg,
                icode->code_span());
            auto result = vm.execute_raw<traits>(rt_ctx, hash, vcode);
            ASSERT_EQ(result.status_code, EVMC_SUCCESS);
            ASSERT_EQ(result.output_size, 0);
        };

    auto [bytecode0, hash0] = make_bytecode(0);
    auto icode0 = make_shared_intercode(bytecode0);
    auto vcode0 = vm.try_insert_varcode(hash0, icode0);

    ASSERT_EQ(vcode0->intercode(), icode0);
    ASSERT_EQ(vcode0->nativecode(), nullptr);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter on cold cache
    execute_raw(EvmTraits<EVMC_HOMESTEAD>{}, hash0, vcode0);

    vm.compiler().debug_wait_for_empty_queue();

    auto compiled_vcode0 = vm.find_varcode(hash0);
    ASSERT_TRUE(compiled_vcode0.has_value());
    ASSERT_EQ(compiled_vcode0.value()->intercode(), icode0);
    ASSERT_NE(compiled_vcode0.value()->nativecode(), nullptr);
    ASSERT_NE(compiled_vcode0.value()->nativecode()->entrypoint(), nullptr);
    ASSERT_EQ(
        compiled_vcode0.value()->nativecode()->chain_id(),
        EvmTraits<EVMC_HOMESTEAD>::id());

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute compiled bytecode on cold cache
    execute_raw(EvmTraits<EVMC_HOMESTEAD>{}, hash0, compiled_vcode0.value());

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter because of revision change
    execute_raw(EvmTraits<EVMC_SHANGHAI>{}, hash0, compiled_vcode0.value());

    vm.compiler().debug_wait_for_empty_queue();

    auto re_compiled_vcode0 = vm.find_varcode(hash0);
    ASSERT_NE(re_compiled_vcode0, compiled_vcode0);
    ASSERT_TRUE(re_compiled_vcode0.has_value());
    ASSERT_EQ(re_compiled_vcode0.value()->intercode(), icode0);
    ASSERT_NE(re_compiled_vcode0.value()->nativecode(), nullptr);
    ASSERT_NE(
        re_compiled_vcode0.value()->nativecode(),
        compiled_vcode0.value()->nativecode());
    ASSERT_NE(re_compiled_vcode0.value()->nativecode()->entrypoint(), nullptr);
    ASSERT_EQ(
        re_compiled_vcode0.value()->nativecode()->chain_id(),
        EvmTraits<EVMC_SHANGHAI>::id());

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute compiled bytecode after revision change
    execute_raw(EvmTraits<EVMC_SHANGHAI>{}, hash0, re_compiled_vcode0.value());

    auto [noncompiling_bytecode, noncompiling_hash] =
        make_bytecode_with_compilation_failure();
    auto noncompiling_icode = make_shared_intercode(noncompiling_bytecode);
    auto noncompiling_vcode =
        vm.try_insert_varcode(noncompiling_hash, noncompiling_icode);

    ASSERT_EQ(noncompiling_vcode->intercode(), noncompiling_icode);
    ASSERT_EQ(noncompiling_vcode->nativecode(), nullptr);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter on cold cache
    execute_raw(
        EvmTraits<EVMC_SHANGHAI>{}, noncompiling_hash, noncompiling_vcode);

    vm.compiler().debug_wait_for_empty_queue();

    auto attempted_noncompiling_vcode = vm.find_varcode(noncompiling_hash);
    ASSERT_TRUE(attempted_noncompiling_vcode.has_value());
    ASSERT_EQ(
        attempted_noncompiling_vcode.value()->intercode(), noncompiling_icode);
    ASSERT_NE(attempted_noncompiling_vcode.value()->nativecode(), nullptr);
    ASSERT_EQ(
        attempted_noncompiling_vcode.value()->nativecode()->chain_id(),
        EvmTraits<EVMC_SHANGHAI>::id());
    ASSERT_EQ(
        attempted_noncompiling_vcode.value()->nativecode()->entrypoint(),
        nullptr);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter after failed compliation
    execute_raw(
        EvmTraits<EVMC_SHANGHAI>{},
        noncompiling_hash,
        attempted_noncompiling_vcode.value());

    // Warm up cache
    for (uint32_t i = 1; i <= warm_kb_threshold / 3; ++i) {
        auto [bc, h] = make_bytecode(i);
        auto ic = make_shared_intercode(bc);
        vm.try_insert_varcode(h, ic);
    }
    ASSERT_TRUE(vm.compiler().is_varcode_cache_warm());

    auto [warm_bytecode, warm_hash] = make_bytecode(warm_kb_threshold / 3 + 1);
    auto warm_icode = make_shared_intercode(warm_bytecode);
    auto warm_vcode = vm.try_insert_varcode(warm_hash, warm_icode);

    auto max_code_size_offset = vm.compiler_config().max_code_size_offset;
    auto const compile_threshold =
        native::max_code_size(max_code_size_offset, warm_icode->code_size());

    // Execute with interpreter on warm cache until compilation is started.
    do {
        execute_raw(EvmTraits<EVMC_SHANGHAI>{}, warm_hash, warm_vcode);
        vm.compiler().debug_wait_for_empty_queue();
    }
    while (warm_vcode->get_intercode_gas_used() < *compile_threshold);

    vm.compiler().debug_wait_for_empty_queue();

    auto compiled_warm_vcode = vm.find_varcode(warm_hash);
    ASSERT_TRUE(compiled_warm_vcode.has_value());
    ASSERT_EQ(compiled_warm_vcode.value()->intercode(), warm_icode);
    ASSERT_NE(compiled_warm_vcode.value()->nativecode(), nullptr);
    ASSERT_NE(compiled_warm_vcode.value()->nativecode()->entrypoint(), nullptr);
    ASSERT_EQ(
        compiled_warm_vcode.value()->nativecode()->chain_id(),
        EvmTraits<EVMC_SHANGHAI>::id());

    ASSERT_TRUE(vm.compiler().is_varcode_cache_warm());

    // Execute compiled bytecode on warm cache
    execute_raw(
        EvmTraits<EVMC_SHANGHAI>{}, warm_hash, compiled_warm_vcode.value());
}

TEST(MonadVmInterface, execute)
{
    // The `VM::execute` is mostly tested already via the test
    // MonadVmInterface.execute_raw

    test::TestMessage msg{};
    msg->gas = 100'000'000'000'000;

    {
        VM vm;
        HostMock host{
            0, [&](Host &, evmc_message const &) { return evmc::Result{}; }};
        std::vector<uint8_t> bytecode{};
        auto hash = std::bit_cast<evmc::bytes32>(
            ethash::keccak256(bytecode.data(), bytecode.size()));
        auto icode = make_shared_intercode(bytecode);
        auto vcode = vm.try_insert_varcode(hash, icode);
        auto result =
            vm.execute<EvmTraits<EVMC_PRAGUE>>(host, &*msg, hash, vcode);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 0);
    }

    std::vector<uint8_t> bytecode = {
        PUSH0, PUSH0, PUSH0, PUSH0, PUSH0, ADDRESS, GAS, CALL};
    auto hash = std::bit_cast<evmc::bytes32>(
        ethash::keccak256(bytecode.data(), bytecode.size()));
    auto icode = make_shared_intercode(bytecode);

    for (size_t const depth : std::initializer_list<size_t>{0, 1, 2, 1023}) {
        VM vm;
        try {
            auto vcode = vm.try_insert_varcode(hash, icode);
            ASSERT_EQ(vcode->intercode(), icode);
            ASSERT_EQ(vcode->nativecode(), nullptr);
            HostMock host{depth, [&](Host &host, evmc_message const &m) {
                              return vm.execute<EvmTraits<EVMC_PRAGUE>>(
                                  host, &m, hash, vcode);
                          }};
            vm.execute<EvmTraits<EVMC_PRAGUE>>(host, &*msg, hash, vcode);
            ASSERT_TRUE(false);
        }
        catch (HostMock::Exception const &e) {
            ASSERT_EQ(e.message, std::string{"exception"});
        }
        catch (...) {
            ASSERT_TRUE(false);
        }
        vm.compiler().debug_wait_for_empty_queue();
        try {
            auto vcode = vm.find_varcode(hash);
            ASSERT_TRUE(vcode.has_value());
            ASSERT_EQ(vcode.value()->intercode(), icode);
            ASSERT_NE(vcode.value()->nativecode(), nullptr);
            HostMock host{depth, [&](Host &host, evmc_message const &m) {
                              return vm.execute<EvmTraits<EVMC_PRAGUE>>(
                                  host, &m, hash, *vcode);
                          }};
            vm.execute<EvmTraits<EVMC_PRAGUE>>(host, &*msg, hash, *vcode);
            ASSERT_TRUE(false);
        }
        catch (HostMock::Exception const &e) {
            ASSERT_EQ(e.message, std::string{"exception"});
        }
        catch (...) {
            ASSERT_TRUE(false);
        }
    }
}

TEST(MonadVmInterface, execute_bytecode)
{
    // The `VM::execute_bytecode` function is mostly tested already via the test
    // MonadVmInterface.execute_bytecode_raw

    VM vm;

    test::TestMessage msg{};
    msg->gas = 100'000'000'000'000;

    {
        HostMock host{
            0, [&](Host &, evmc_message const &) { return evmc::Result{}; }};
        std::vector<uint8_t> bytecode{};
        auto result =
            vm.execute_bytecode<EvmTraits<EVMC_PRAGUE>>(host, &*msg, bytecode);
        ASSERT_EQ(result.status_code, EVMC_SUCCESS);
        ASSERT_EQ(result.output_size, 0);
    }

    std::vector<uint8_t> bytecode = {
        PUSH0, PUSH0, PUSH0, PUSH0, PUSH0, ADDRESS, GAS, CALL};

    for (size_t const depth : std::initializer_list<size_t>{0, 1, 2, 1023}) {
        try {
            HostMock host{
                depth, [&](Host &host, evmc_message const &m) {
                    return vm.execute_bytecode<EvmTraits<EVMC_PRAGUE>>(
                        host, &m, bytecode);
                }};
            vm.execute_bytecode<EvmTraits<EVMC_PRAGUE>>(host, &*msg, bytecode);
            ASSERT_TRUE(false);
        }
        catch (HostMock::Exception const &e) {
            ASSERT_EQ(e.message, std::string{"exception"});
        }
        catch (...) {
            ASSERT_TRUE(false);
        }
    }
}

TEST(MonadVmInterface, message_memory)
{
    VM vm;
    auto const capacity = vm.message_memory_capacity();
    ASSERT_EQ(capacity, 8 * 1024 * 1024);
    {
        auto mem1 = vm.message_memory_ref();
        ASSERT_EQ(mem1.get()[capacity - 1], 0);
        ASSERT_EQ(mem1.get()[0], 0);
        mem1.get()[capacity - 1] = 1;
        mem1.get()[0] = 2;
        {
            auto mem2 = vm.message_memory_ref();
            ASSERT_EQ(mem2.get()[capacity - 1], 0);
            ASSERT_EQ(mem2.get()[0], 0);
        }
        ASSERT_EQ(mem1.get()[capacity - 1], 1);
        ASSERT_EQ(mem1.get()[0], 2);
        // Technically it may not be necessary to clear memory here, but
        // under the normal circumstances it is an invariant that memory
        // is cleared before it is deallocated:
        mem1.get()[capacity - 1] = 0;
        mem1.get()[0] = 0;
    }
}
