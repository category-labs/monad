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

#pragma once

#include <category/vm/code.hpp>
#include <category/vm/utils/evmc_utils.hpp>
#include <category/vm/utils/lru_weight_cache.hpp>

#include <span>

namespace monad::vm
{
    class VarcodeCache
    {
        static constexpr std::uint32_t default_max_cache_kb =
            std::uint32_t{1} << 22; // 4MB * 1kB = 4GB

        static constexpr std::uint32_t default_warm_cache_kb =
            (3 * default_max_cache_kb) / 4; // ~75%

        using WeightCache = utils::LruWeightCache<
            evmc::bytes32, SharedVarcode, utils::Hash32Compare>;

    public:
        explicit VarcodeCache(
            std::uint32_t max_cache_kb = default_max_cache_kb,
            std::uint32_t warm_cache_kb = default_warm_cache_kb);

        /// Get varcode for given code hash.
        std::optional<SharedVarcode> get(evmc::bytes32 const &code_hash);

        /// Insert into cache under `code_hash`.
        void
        set(evmc::bytes32 const &code_hash, SharedIntercode const &,
            SharedNativecode const &);

        /// Find varcode under `code_hash`, otherwise insert into cache.
        SharedVarcode
        try_set(evmc::bytes32 const &code_hash, SharedIntercode const &);

        /// Find varcode under `code_hash`, otherwise construct a
        /// `SharedVarcode` object from the given bytecodes and insert it into
        /// cache.
        SharedVarcode try_set_raw(
            evmc::bytes32 const &code_hash, std::span<uint8_t const> code);

        /// Whether the cache is warmed up.
        bool is_warm()
        {
            return weight_cache_.approx_weight() >= warm_cache_kb_;
        }

        void set_warm_cache_kb(std::uint32_t warm_kb)
        {
            warm_cache_kb_ = warm_kb;
        }

        // Cache weight of the given code size.
        static std::uint32_t code_size_to_cache_weight(std::uint32_t code_size);

        /// Get approximate total weight of the cached elements.
        uint64_t approx_weight() const
        {
            return weight_cache_.approx_weight();
        }

        /// Return the number of cached elements.
        size_t size() const noexcept
        {
            return weight_cache_.size();
        }

    private:
        WeightCache weight_cache_;
        std::uint32_t warm_cache_kb_;
    };
}
