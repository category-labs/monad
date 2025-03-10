#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>

#include <type_traits>

MONAD_NAMESPACE_BEGIN

template <typename T>
constexpr size_t num_storage_slots()
{
    constexpr size_t SLOT_SIZE = sizeof(bytes32_t);
    return (sizeof(T) + SLOT_SIZE - 1) / SLOT_SIZE;
}

// This type abstracts storage any T type across the minimum number of EVM
// storage slots required to store that type.
template <typename T>
    requires std::is_trivially_copyable_v<T>
struct StorageAdapter
{
    static constexpr size_t N = num_storage_slots<T>();

    union
    {
        struct
        {
            bytes32_t raw[N];

            constexpr size_t size() const noexcept
            {
                return N;
            }

            constexpr bytes32_t &operator[](size_t const i) noexcept
            {
                return raw[i];
            }

            constexpr bytes32_t const &operator[](size_t const i) const noexcept
            {
                return raw[i];
            }

        } slots;

        T typed;
    };

    StorageAdapter()
        : typed{}
    {
    }
};

// A class for generating keys for storage slot, prefixed by the validators ETH
// address. The layout is:
//  [ 11 zero bytes, 20 bytes for address, 1 byte for slot index ]
class ValidatorStorageKeyGenerator
{
    bytes32_t key_;

public:
    ValidatorStorageKeyGenerator(Address const &address)
    {
        std::memcpy(
            key_.bytes + sizeof(key_.bytes) - sizeof(Address) - 1,
            address.bytes,
            sizeof(Address));
    }

    bytes32_t const &key(uint8_t const i)
    {
        key_.bytes[31] = i;
        return key_;
    }
};

MONAD_NAMESPACE_END
