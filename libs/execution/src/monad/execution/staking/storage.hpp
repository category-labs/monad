#pragma once

#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state3/state.hpp>

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

// An array in the State trie. First index is the size.
template <typename T>
class StorageArray
{
    State &state_;
    Address const &address_;
    uint256_t const slot_;

    static constexpr size_t NUM_SLOTS = num_storage_slots<T>();

public:
    StorageArray(State &state, Address const &address, bytes32_t const &slot)
        : state_{state}
        , address_{address}
        , slot_{intx::be::load<uint256_t>(slot)}
    {
    }

    uint64_t size() const noexcept
    {
        bytes32_t const size_padded =
            state_.get_storage(address_, to_bytes(slot_));
        return ::evmc::load64be(
            size_padded.bytes + sizeof(size_padded.bytes) - sizeof(uint64_t));
    }

    T operator[](uint64_t const index) const noexcept
    {
        StorageAdapter<T> adapter;
        size_t offset = 1 /* length */ + index * NUM_SLOTS;
        for (size_t i = 0; i < NUM_SLOTS; ++i) {
            adapter.slots[i] =
                state_.get_storage(address_, to_bytes(slot_ + offset + i));
        }
        return adapter.typed;
    }

    void push(T const &elem) noexcept
    {
        StorageAdapter<T> adapter;
        adapter.typed = elem;
        size_t num_elements = size();
        size_t offset = 1 /* length */ + num_elements * NUM_SLOTS;

        // set slots
        for (size_t i = 0; i < NUM_SLOTS; ++i) {
            state_.set_storage(
                address_, to_bytes(slot_ + offset + i), adapter.slots[i]);
        }

        // increment count
        state_.set_storage(
            address_, to_bytes(slot_), bytes32_t{num_elements + 1});
    }

    void pop() noexcept
    {
        size_t num_elements = size();
        if (num_elements > 0) {
            size_t offset = 1 /* length */ + (num_elements - 1) * NUM_SLOTS;

            // clear slots
            for (size_t i = 0; i < NUM_SLOTS; ++i) {
                state_.set_storage(
                    address_, to_bytes(slot_ + offset + i), bytes32_t{});
            }

            // decrement count
            state_.set_storage(
                address_, to_bytes(slot_), bytes32_t{num_elements - 1});
        }
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
