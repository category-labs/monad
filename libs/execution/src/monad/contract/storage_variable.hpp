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
            state_.set_storage(address_, key_, adapter.slots[i]);
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
        bool has_data = false;
        for (size_t i = 0; i < N; ++i) {
            value.slots[i] = state_.get_storage(address_, key_);
            has_data |= (value.slots[i] != bytes32_t{});
        }
        return has_data ? value.typed : std::optional<T>{};
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
