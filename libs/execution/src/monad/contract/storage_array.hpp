#pragma once

#include <monad/config.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state3/state.hpp>

#include <intx/intx.hpp>

MONAD_NAMESPACE_BEGIN

// An array in the State trie. First index is the size.
template <typename T>
class StorageArray
{
    State &state_;
    Address const &address_;
    StorageVariable<uint256_t> length_;
    uint256_t const start_index_;

    static constexpr size_t NUM_SLOTS = num_storage_slots<T>();

public:
    StorageArray(State &state, Address const &address, bytes32_t const &slot)
        : state_{state}
        , address_{address}
        , length_{StorageVariable<uint256_t>(state, address, slot)}
        , start_index_{intx::be::load<uint256_t>(slot.bytes) + 1}
    {
    }

    uint256_t length() const noexcept
    {
        return length_.load();
    }

    StorageVariable<T> get(uint256_t const index) const noexcept
    {
        auto const length = length_.load();
        MONAD_ASSERT(index < length);

        auto const offset = start_index_ + index * NUM_SLOTS;
        return StorageVariable<T>{
            state_, address_, intx::be::store<bytes32_t>(offset)};
    }

    void push(T const &value) noexcept
    {
        auto const length = length_.load();
        auto const offset = start_index_ + length * NUM_SLOTS;
        StorageVariable<T> var{
            state_, address_, intx::be::store<bytes32_t>(offset)};
        var.store(value);
        length_.store(length + 1);
    }

    T pop() noexcept
    {
        auto const length = length_.load();
        MONAD_ASSERT(length > 0);
        auto var = get(length - 1);
        auto value = var.load();
        var.clear();
        length_.store(length - 1);
        return value;
    }
};

MONAD_NAMESPACE_END