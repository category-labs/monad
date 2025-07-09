#include <monad/vm/code.hpp>
#include <monad/vm/varcode_cache.hpp>

#include <asmjit/core/jitruntime.h>

#include <ethash/keccak.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

using namespace monad::vm;

namespace
{
    std::pair<std::vector<uint8_t>, evmc::bytes32> make_bytecode(uint8_t byte)
    {
        std::vector<uint8_t> bytecode{byte};
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
