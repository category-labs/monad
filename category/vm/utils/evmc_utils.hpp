#pragma once

#include <evmc/evmc.hpp>

namespace monad::vm::utils
{
    inline std::size_t hash32_hash(evmc::bytes32 const &hash32)
    {
        static_assert(sizeof(std::size_t) >= sizeof(uint64_t));
        std::uint64_t result;
        std::memcpy(&result, hash32.bytes, 8);
        std::uint64_t tmp;
        std::memcpy(&tmp, hash32.bytes + 8, 8);
        result ^= tmp;
        std::memcpy(&tmp, hash32.bytes + 16, 8);
        result ^= tmp;
        std::memcpy(&tmp, hash32.bytes + 24, 8);
        result ^= tmp;
        return result;
    }

    struct Hash32Hash
    {
        std::size_t operator()(evmc::bytes32 const &hash32) const
        {
            return hash32_hash(hash32);
        }
    };

    struct Bytes32Equal
    {
        bool operator()(evmc::bytes32 const &x, evmc::bytes32 const &y) const
        {
            return x == y;
        }
    };

    struct Hash32Compare
    {
        std::size_t hash(evmc::bytes32 const &hash32) const
        {
            return hash32_hash(hash32);
        }

        bool equal(evmc::bytes32 const &x, evmc::bytes32 const &y) const
        {
            return x == y;
        }
    };

    std::string hex_string(evmc::bytes32 const &);
    std::string hex_string(evmc::address const &);
}
