#include <monad/state2/state_ops.hpp>

#include <monad/core/assert.h>
#include <monad/core/likely.h>

#include <mutex>
#include <shared_mutex>

MONAD_NAMESPACE_BEGIN

template <class Mutex>
std::optional<Account> read_account(
    address_t const &address, State &state, BlockState<Mutex> &block_state,
    Db &db)
{
    // state
    {
        auto const it = state.find(address);
        if (MONAD_LIKELY(it != state.end())) {
            auto const &result = it->second.account.second;
            return result;
        }
    }
    // block state
    {
        std::shared_lock<Mutex> const lock{block_state.mutex};
        auto const it = block_state.state.find(address);
        if (MONAD_LIKELY(it != block_state.state.end())) {
            auto const &result = it->second.account.second;
            state[address] = {.account = {result, result}, .storage = {}};
            return result;
        }
    }
    // database
    auto result = db.read_account(address);
    {
        std::lock_guard<Mutex> const lock{block_state.mutex};
        auto const [it, inserted] = block_state.state.try_emplace(
            address, AccountState{.account = {result, result}, .storage = {}});
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second.account.second;
        }
    }
    state[address] = {.account = {result, result}, .storage = {}};
    return result;
}

template <class Mutex>
bytes32_t read_storage(
    address_t const &address, uint64_t const incarnation,
    bytes32_t const &location, State &state, BlockState<Mutex> &block_state,
    Db &db)
{
    // state
    auto const it = state.find(address);
    MONAD_ASSERT(it != state.end());
    auto &storage = it->second.storage;
    {
        auto const it = storage.find(location);
        if (MONAD_LIKELY(it != storage.end())) {
            auto const &result = it->second.second;
            return result;
        }
    }
    // block state
    {
        std::shared_lock<Mutex> const lock{block_state.mutex};
        auto const it = block_state.state.find(address);
        MONAD_ASSERT(it != block_state.state.end());
        auto &block_storage = it->second.storage;
        {
            auto const it = block_storage.find(location);
            if (MONAD_LIKELY(it != block_storage.end())) {
                auto const &result = it->second.second;
                storage[location] = {result, result};
                return result;
            }
        }
    }
    // database
    auto result = db.read_storage(address, incarnation, location);
    {
        std::lock_guard<Mutex> const lock{block_state.mutex};
        auto const it = block_state.state.find(address);
        MONAD_ASSERT(it != block_state.state.end());
        auto &block_storage = it->second.storage;
        {
            auto const [it, inserted] =
                block_storage.try_emplace(location, result, result);
            if (MONAD_UNLIKELY(!inserted)) {
                result = it->second.second;
            }
        }
    }
    storage[location] = {result, result};
    return result;
}

template std::optional<Account>
read_account(address_t const &, State &, BlockState<std::shared_mutex> &, Db &);

template bytes32_t read_storage(
    address_t const &, uint64_t, bytes32_t const &, State &,
    BlockState<std::shared_mutex> &, Db &);

MONAD_NAMESPACE_END
