#include <category/vm/code.hpp>
#include <category/vm/core/assert.h>
#include <category/vm/varcode_cache.hpp>

#include <evmc/evmc.hpp>

#include <cstddef>
#include <cstdint>
#include <limits>
#include <memory>
#include <optional>

namespace monad::vm
{
    std::uint32_t VarcodeCache::code_size_to_cache_weight(std::size_t code_size)
    {
        MONAD_VM_DEBUG_ASSERT(
            code_size <= std::numeric_limits<uint32_t>::max());
        // Byte size in kB, plus 3 kB overhead:
        return (static_cast<std::uint32_t>(code_size) >> 10) + 3;
    }

    VarcodeCache::VarcodeCache(std::uint32_t max_kb, std::uint32_t warm_kb)
        : weight_cache_{max_kb}
        , warm_cache_kb_{warm_kb}
    {
    }

    std::optional<SharedVarcode>
    VarcodeCache::get(evmc::bytes32 const &code_hash)
    {
        WeightCache::ConstAccessor acc;
        if (!weight_cache_.find(acc, code_hash)) {
            return std::nullopt;
        }
        return acc->second.value_;
    }

    void VarcodeCache::set(
        evmc::bytes32 const &code_hash, SharedIntercode const &icode,
        SharedNativecode const &ncode)
    {
        MONAD_VM_ASSERT(icode != nullptr);
        MONAD_VM_ASSERT(ncode != nullptr);
        auto weight = code_size_to_cache_weight(
            icode->code_size() + ncode->code_size_estimate());
        auto vcode = std::make_shared<Varcode>(icode, ncode);
        weight_cache_.insert(code_hash, vcode, weight);
    }

    SharedVarcode VarcodeCache::try_set(
        evmc::bytes32 const &code_hash, SharedIntercode const &icode)
    {
        MONAD_VM_ASSERT(icode != nullptr);
        auto weight = code_size_to_cache_weight(icode->code_size());
        auto vcode = std::make_shared<Varcode>(icode);
        (void)weight_cache_.try_insert(code_hash, vcode, weight);
        return vcode;
    }
}
