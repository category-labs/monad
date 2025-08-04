#include <category/vm/code.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/varcode_cache.hpp>
#include <category/vm/vm.hpp>

#include <asmjit/core/jitruntime.h>

#include <ethash/keccak.hpp>

#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

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
}

TEST(MonadVmInterface, VarcodeCache)
{
    static uint32_t const bytecode_cache_weight = 3;
    static uint32_t const warm_cache_kb = 2 * bytecode_cache_weight;
    static uint32_t const max_cache_kb = warm_cache_kb;

    VarcodeCache cache{max_cache_kb, warm_cache_kb};
    auto [bytecode0, hash0] = make_bytecode(0);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(bytecode0.size()),
        bytecode_cache_weight);
    auto icode0 = make_shared_intercode(bytecode0);
    asmjit::JitRuntime asmjit_rt;
    auto ncode0 =
        std::make_shared<Nativecode>(asmjit_rt, EVMC_FRONTIER, nullptr, 0);

    ASSERT_FALSE(cache.get(hash0).has_value());
    cache.set(hash0, icode0, ncode0);

    ASSERT_FALSE(cache.is_warm());

    auto vcode0 = cache.get(hash0);

    ASSERT_TRUE(vcode0.has_value());
    ASSERT_EQ(vcode0.value()->intercode(), icode0);
    ASSERT_EQ(vcode0.value()->nativecode(), ncode0);
    ASSERT_EQ(vcode0, cache.get(hash0));

    auto [bytecode1, hash1] = make_bytecode(1);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(bytecode1.size()),
        bytecode_cache_weight);
    auto icode1 = make_shared_intercode(bytecode1);

    auto vcode1 = cache.try_set(hash1, icode1);

    ASSERT_TRUE(cache.is_warm());

    ASSERT_NE(vcode0.value(), vcode1);
    ASSERT_EQ(vcode1->intercode(), icode1);
    ASSERT_EQ(vcode1->nativecode(), nullptr);
    ASSERT_EQ(vcode1, cache.get(hash1).value());
    ASSERT_EQ(vcode0, cache.get(hash0).value());

    auto [bytecode2, hash2] = make_bytecode(2);
    ASSERT_EQ(
        VarcodeCache::code_size_to_cache_weight(bytecode2.size()),
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
}

TEST(MonadVmInterface, compile)
{
    VM vm;

    auto [bytecode1, hash1] = make_bytecode(1);
    auto icode1 = make_shared_intercode(bytecode1);

    auto ncode1 = vm.compiler().compile(EVMC_FRONTIER, icode1);
    auto entry1 = ncode1->entrypoint();
    ASSERT_NE(entry1, nullptr);

    auto ctx1 = runtime::Context::empty();
    entry1(&ctx1, nullptr);

    ASSERT_EQ(uint256_t::load_le(ctx1.result.size), 0);
    ASSERT_EQ(uint256_t::load_le(ctx1.result.offset), 1);

    ASSERT_FALSE(vm.find_varcode(hash1).has_value());
}

TEST(MonadVmInterface, cached_compile)
{
    VM vm;

    auto [bytecode1, hash1] = make_bytecode(1);
    auto icode1 = make_shared_intercode(bytecode1);

    auto ncode1 = vm.compiler().cached_compile(EVMC_FRONTIER, hash1, icode1);
    auto entry1 = ncode1->entrypoint();
    ASSERT_NE(entry1, nullptr);

    auto ctx1 = runtime::Context::empty();
    entry1(&ctx1, nullptr);

    ASSERT_EQ(uint256_t::load_le(ctx1.result.size), 0);
    ASSERT_EQ(uint256_t::load_le(ctx1.result.offset), 1);

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

        ASSERT_TRUE(vm.compiler().async_compile(EVMC_FRONTIER, hash1, icode1));
        vm.compiler().debug_wait_for_empty_queue();

        auto vcode1 = vm.find_varcode(hash1);
        ASSERT_TRUE(vcode1.has_value());
        ASSERT_EQ(vcode1.value()->intercode(), icode1);
        ASSERT_NE(vcode1.value()->nativecode(), nullptr);

        auto entry1 = (*vcode1)->nativecode()->entrypoint();
        if (enabled) {
            ASSERT_NE(entry1, nullptr);
            auto ctx1 = runtime::Context::empty();
            entry1(&ctx1, nullptr);
            ASSERT_EQ(uint256_t::load_le(ctx1.result.size), 0);
            ASSERT_EQ(uint256_t::load_le(ctx1.result.offset), 1);
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
}

TEST(MonadVmInterface, execute_raw)
{
    VM vm;
    evmc::MockedHost host;

    auto [bytecode0, hash0] = make_bytecode(0);

    evmc_message msg{};
    msg.gas = 10;

    auto result = vm.execute_raw(
        EVMC_FRONTIER,
        &host.get_interface(),
        host.to_context(),
        &msg,
        {bytecode0.data(), bytecode0.size()});
    ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    ASSERT_EQ(result.output_size, 0);
    ASSERT_EQ(result.gas_left, 4);
}

TEST(MonadVmInterface, execute_intercode)
{
    VM vm;
    evmc::MockedHost host;

    auto [bytecode0, hash0] = make_bytecode(0);
    auto icode0 = make_shared_intercode(bytecode0);

    evmc_message msg{};
    msg.gas = 10;

    auto result = vm.execute_intercode(
        EVMC_FRONTIER, &host.get_interface(), host.to_context(), &msg, icode0);
    ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    ASSERT_EQ(result.output_size, 0);
    ASSERT_EQ(result.gas_left, 4);
}

TEST(MonadVmInterface, execute_native_entrypoint)
{
    VM vm;
    evmc::MockedHost host;

    auto [bytecode0, hash0] = make_bytecode(0);
    auto icode0 = make_shared_intercode(bytecode0);
    auto ncode0 = vm.compiler().compile(EVMC_FRONTIER, icode0);
    auto entry0 = ncode0->entrypoint();
    ASSERT_NE(entry0, nullptr);

    evmc_message msg{};
    msg.gas = 10;

    auto result = vm.execute_native_entrypoint(
        &host.get_interface(), host.to_context(), &msg, icode0, entry0);
    ASSERT_EQ(result.status_code, EVMC_SUCCESS);
    ASSERT_EQ(result.output_size, 0);
    ASSERT_EQ(result.gas_left, 4);
}

TEST(MonadVmInterface, execute)
{
    VM vm;
    evmc::MockedHost host;

    evmc_message msg{};
    msg.gas = 100'000'000;

    static uint32_t const warm_kb_threshold = 1 << 10; // 1MB
    vm.compiler().set_varcode_cache_warm_kb_threshold(warm_kb_threshold);

    auto execute = [&](evmc_revision rev,
                       evmc::bytes32 const &hash,
                       SharedVarcode const &vcode) {
        auto result = vm.execute(
            rev, &host.get_interface(), host.to_context(), &msg, hash, vcode);
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
    execute(EVMC_FRONTIER, hash0, vcode0);

    vm.compiler().debug_wait_for_empty_queue();

    auto compiled_vcode0 = vm.find_varcode(hash0);
    ASSERT_TRUE(compiled_vcode0.has_value());
    ASSERT_EQ(compiled_vcode0.value()->intercode(), icode0);
    ASSERT_NE(compiled_vcode0.value()->nativecode(), nullptr);
    ASSERT_NE(compiled_vcode0.value()->nativecode()->entrypoint(), nullptr);
    ASSERT_EQ(compiled_vcode0.value()->nativecode()->revision(), EVMC_FRONTIER);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute compiled bytecode on cold cache
    execute(EVMC_FRONTIER, hash0, compiled_vcode0.value());

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter because of revision change
    execute(EVMC_SHANGHAI, hash0, compiled_vcode0.value());

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
        re_compiled_vcode0.value()->nativecode()->revision(), EVMC_SHANGHAI);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute compiled bytecode after revision change
    execute(EVMC_SHANGHAI, hash0, re_compiled_vcode0.value());

    auto [noncompiling_bytecode, noncompiling_hash] =
        make_bytecode_with_compilation_failure();
    auto noncompiling_icode = make_shared_intercode(noncompiling_bytecode);
    auto noncompiling_vcode =
        vm.try_insert_varcode(noncompiling_hash, noncompiling_icode);

    ASSERT_EQ(noncompiling_vcode->intercode(), noncompiling_icode);
    ASSERT_EQ(noncompiling_vcode->nativecode(), nullptr);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter on cold cache
    execute(EVMC_SHANGHAI, noncompiling_hash, noncompiling_vcode);

    vm.compiler().debug_wait_for_empty_queue();

    auto attempted_noncompiling_vcode = vm.find_varcode(noncompiling_hash);
    ASSERT_TRUE(attempted_noncompiling_vcode.has_value());
    ASSERT_EQ(
        attempted_noncompiling_vcode.value()->intercode(), noncompiling_icode);
    ASSERT_NE(attempted_noncompiling_vcode.value()->nativecode(), nullptr);
    ASSERT_EQ(
        attempted_noncompiling_vcode.value()->nativecode()->revision(),
        EVMC_SHANGHAI);
    ASSERT_EQ(
        attempted_noncompiling_vcode.value()->nativecode()->entrypoint(),
        nullptr);

    ASSERT_FALSE(vm.compiler().is_varcode_cache_warm());

    // Execute with interpreter after failed compliation
    execute(
        EVMC_SHANGHAI, noncompiling_hash, attempted_noncompiling_vcode.value());

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
        execute(EVMC_SHANGHAI, warm_hash, warm_vcode);
        vm.compiler().debug_wait_for_empty_queue();
    }
    while (warm_vcode->get_intercode_gas_used() < compile_threshold);

    vm.compiler().debug_wait_for_empty_queue();

    auto compiled_warm_vcode = vm.find_varcode(warm_hash);
    ASSERT_TRUE(compiled_warm_vcode.has_value());
    ASSERT_EQ(compiled_warm_vcode.value()->intercode(), warm_icode);
    ASSERT_NE(compiled_warm_vcode.value()->nativecode(), nullptr);
    ASSERT_NE(compiled_warm_vcode.value()->nativecode()->entrypoint(), nullptr);
    ASSERT_EQ(
        compiled_warm_vcode.value()->nativecode()->revision(), EVMC_SHANGHAI);

    ASSERT_TRUE(vm.compiler().is_varcode_cache_warm());

    // Execute compiled bytecode on warm cache
    execute(EVMC_SHANGHAI, warm_hash, compiled_warm_vcode.value());
}
