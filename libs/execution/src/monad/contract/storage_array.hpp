#pragma once

#include <monad/config.hpp>
#include <monad/contract/storage_variable.hpp>
#include <monad/contract/uint256.hpp>
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
    StorageVariable<Uint256BE> length_;
    uint256_t const start_index_;

    static constexpr size_t NUM_SLOTS = num_storage_slots<T>();

public:
    StorageArray(State &state, Address const &address, bytes32_t const &slot)
        : state_{state}
        , address_{address}
        , length_{StorageVariable<Uint256BE>(state, address, slot)}
        , start_index_{intx::be::load<uint256_t>(slot.bytes) + 1}
    {
    }

    Uint256Native length() const noexcept
    {
        auto const len = length_.load();
        if (MONAD_UNLIKELY(!len.has_value())) {
            return 0;
        }
        return len.value().native();
    }

    bool empty() const noexcept
    {
        return length() == 0;
    }

    StorageVariable<T> get(uint256_t const index) const noexcept
    {
        MONAD_ASSERT(index < length());

        auto const offset = start_index_ + index * NUM_SLOTS;
        return StorageVariable<T>{
            state_, address_, intx::be::store<bytes32_t>(offset)};
    }

    void push(T const &value) noexcept
    {
        Uint256Native len = length();
        auto const offset = start_index_ + len * NUM_SLOTS;
        StorageVariable<T> var{
            state_, address_, intx::be::store<bytes32_t>(offset)};
        var.store(value);
        length_.store(len.add(1).to_be());
    }

    T pop() noexcept
    {
        Uint256Native len = length();
        MONAD_ASSERT(len > 0);
        len = len.sub(1);

        auto var = get(len);
        auto value = var.load().value();
        var.clear();
        length_.store(len.to_be());
        return value;
    }
};

MONAD_NAMESPACE_END
