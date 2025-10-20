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
#include <category/vm/core/assert.h>
#include <category/vm/varcode_cache.hpp>

#include <evmc/evmc.hpp>

#include <cstdint>
#include <memory>
#include <optional>

namespace monad::vm
{
    std::uint32_t
    VarcodeCache::code_size_to_cache_weight(std::uint32_t code_size)
    {
        // Byte size in kB, plus 3 kB overhead:
        return (code_size >> 10) + 3;
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
        auto const weight = code_size_to_cache_weight(
            *(icode->code_size() + ncode->code_size_estimate()));
        auto const vcode = std::make_shared<Varcode>(icode, ncode);
        weight_cache_.insert(code_hash, vcode, weight);
    }

    SharedVarcode VarcodeCache::try_set(
        evmc::bytes32 const &code_hash, SharedIntercode const &icode)
    {
        MONAD_VM_ASSERT(icode != nullptr);
        auto const weight = code_size_to_cache_weight(*icode->code_size());
        auto vcode = std::make_shared<Varcode>(icode);
        (void)weight_cache_.try_insert(code_hash, vcode, weight);
        return vcode;
    }
}
