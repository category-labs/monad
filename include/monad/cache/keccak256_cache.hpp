#pragma once

#include <monad/core/byte_string.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/lru/lru_cache.hpp>

#include <ethash/keccak.hpp>

MONAD_NAMESPACE_BEGIN

namespace
{

template <class T>
requires std::same_as<T, bytes32_t> || std::same_as<T, Address>
constexpr byte_string to_key(T const &arg)
{
    return byte_string{
        std::bit_cast<bytes32_t>(
            ethash::keccak256(arg.bytes, sizeof(arg.bytes)))
        .bytes,
        sizeof(bytes32_t)};
}

} /// namespace

template <class T>
requires std::same_as<T, bytes32_t> || std::same_as<T, Address>
class Keccak256Cache
{
    /// TYPES
    using Cache = LruCache<T, byte_string>;
    using ConstAccessor = Cache::ConstAccessor;

    /// DATA
    Cache cache_;

public:

    Keccak256Cache(size_t max_size)
    : cache_(max_size)
    {
    }

    byte_string operator()(T const &arg)
    {
        {
            ConstAccessor acc{};
            if (cache_.find(acc, arg))
            {
                return *acc;
            }
        }
        auto const result = to_key(arg);
        cache_.insert(arg, result);
        return result;
    }

    std::string print_stats()
    {
        return cache_.print_stats();
    }
}; /// Keccak256Cache

MONAD_NAMESPACE_END
