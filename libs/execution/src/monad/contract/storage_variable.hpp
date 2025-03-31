#pragma once

#include <monad/config.hpp>
#include <monad/contract/storage_adapter.hpp>
#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/state3/state.hpp>

#include <intx/intx.hpp>

#include <algorithm>
#include <optional>

MONAD_NAMESPACE_BEGIN

template <typename T>
class StorageVariable
{
    State &state_;
    Address const &address_;
    bytes32_t const key_;

    void store_(StorageAdapter<T> const &adapter)
    {
        for (size_t i = 0; i < N; ++i) {
            state_.set_storage(
                address_, key_, intx::be::store<bytes32_t>(adapter.slots[i]));
        }
    }

public:
    static constexpr size_t N = num_storage_slots<T>();

    StorageVariable(State &state, Address const &address, bytes32_t key)
        : state_{state}
        , address_{address}
        , key_{std::move(key)}
    {
    }

    std::optional<T> load() const noexcept
    {
        StorageAdapter<T> value;
        for (size_t i = 0; i < N; ++i) {
            value.slots[i] =
                intx::be::load<uint256_t>(state_.get_storage(address_, key_));
        }
        return std::all_of(
                   value.slots.raw,
                   value.slots.raw + N,
                   [](uint256_t const &slot) { return slot == 0; })
                   ? std::optional<T>{}
                   : value.typed;
    }

    void store(T const &value)
    {
        StorageAdapter<T> adapter(value);
        store_(adapter);
    }

    void clear()
    {
        StorageAdapter<T> adapter{};
        store_(adapter);
    }
};

MONAD_NAMESPACE_END
