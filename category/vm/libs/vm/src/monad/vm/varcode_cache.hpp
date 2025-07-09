#pragma once

#include <monad/vm/code.hpp>
#include <monad/vm/utils/evmc_utils.hpp>
#include <monad/vm/utils/lru_weight_cache.hpp>

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
        static std::uint32_t code_size_to_cache_weight(std::size_t code_size);

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

        /// Whether the cache is warmed up.
        bool is_warm()
        {
            return weight_cache_.approx_weight() >= warm_cache_kb_;
        }

    private:
        WeightCache weight_cache_;
        std::uint32_t warm_cache_kb_;
    };
}
