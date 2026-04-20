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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/vm/code.hpp>
#include <category/vm/varcode_cache.hpp>

#include <cstdint>
#include <memory>
#include <optional>
#include <span>

namespace monad::vm
{
    uint32_t VarcodeCache::code_size_to_cache_weight(uint32_t const code_size)
    {
        // Byte size in kB, plus 3 kB overhead:
        return (code_size >> 10) + 3;
    }

    VarcodeCache::VarcodeCache(uint32_t const max_kb, uint32_t const warm_kb)
        : weight_cache_{max_kb}
        , warm_cache_kb_{warm_kb}
    {
    }

    std::optional<SharedVarcode> VarcodeCache::get(bytes32_t const &code_hash)
    {
        WeightCache::ConstAccessor acc;
        if (!weight_cache_.find(acc, code_hash)) {
            return std::nullopt;
        }
        return acc->second.value_;
    }

    void VarcodeCache::set(
        bytes32_t const &code_hash, SharedIntercode const &icode,
        SharedNativecode const &ncode)
    {
        MONAD_ASSERT(icode != nullptr);
        MONAD_ASSERT(ncode != nullptr);
        auto const weight = code_size_to_cache_weight(
            *(icode->code_size() + ncode->code_size_estimate()));
        auto const vcode = std::make_shared<Varcode>(icode, ncode);
        weight_cache_.insert(code_hash, vcode, weight);
    }

    SharedVarcode VarcodeCache::try_set(
        bytes32_t const &code_hash, SharedIntercode const &icode)
    {
        MONAD_ASSERT(icode != nullptr);
        auto const weight = code_size_to_cache_weight(*icode->code_size());
        auto vcode = std::make_shared<Varcode>(icode);
        (void)weight_cache_.try_insert(code_hash, vcode, weight);
        return vcode;
    }

    SharedVarcode VarcodeCache::try_set_raw(
        bytes32_t const &code_hash, std::span<uint8_t const> const code)
    {
        WeightCache::ConstAccessor acc;
        if (!weight_cache_.find(acc, code_hash)) {
            return try_set(code_hash, make_shared_intercode(code));
        }
        return acc->second.value_;
    }
}
