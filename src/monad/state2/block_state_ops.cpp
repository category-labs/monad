#include <monad/state2/block_state_ops.hpp>

#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>

#include <mutex>
#include <shared_mutex>

MONAD_NAMESPACE_BEGIN

template <class Mutex>
std::optional<Account> &read_account(
    address_t const &address, StateDeltas &state,
    BlockState<Mutex> &block_state, Db &db)
{
    // state
    {
        auto const it = state.find(address);
        if (MONAD_LIKELY(it != state.end())) {
            auto &result = it->second.account.second;
            return result;
        }
    }
    // block state
    {
        std::shared_lock<Mutex> const lock{block_state.mutex};
        auto const it = block_state.state.find(address);
        if (MONAD_LIKELY(it != block_state.state.end())) {
            auto const &result = it->second.account.second;
            auto const [it, _] = state.try_emplace(
                address,
                StateDelta{.account = {result, result}, .storage = {}});
            return it->second.account.second;
        }
    }
    // database
    auto result = db.read_account(address);
    {
        std::lock_guard<Mutex> const lock{block_state.mutex};
        auto const [it, inserted] = block_state.state.try_emplace(
            address, StateDelta{.account = {result, result}, .storage = {}});
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second.account.second;
        }
    }
    auto const [it, _] = state.try_emplace(
        address, StateDelta{.account = {result, result}, .storage = {}});
    return it->second.account.second;
}

template <class Mutex>
delta_t<bytes32_t> &read_storage(
    address_t const &address, uint64_t const /*incarnation*/,
    bytes32_t const &location, StateDeltas &state,
    BlockState<Mutex> &block_state, Db &db)
{
    // state
    auto const it = state.find(address);
    MONAD_ASSERT(it != state.end());
    auto &storage = it->second.storage;
    {
        auto const it = storage.find(location);
        if (MONAD_LIKELY(it != storage.end())) {
            auto &result = it->second;
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
                auto const [it2, _] =
                    storage.try_emplace(location, result, result);
                return it2->second;
            }
        }
    }
    // database
    auto result = db.read_storage(address, location);
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
    auto const [it2, _] = storage.try_emplace(location, result, result);
    return it2->second;
}

template <class Mutex>
byte_string &read_code(
    bytes32_t const &hash, Code &code, BlockState<Mutex> &block_state, Db &db)
{
    // code
    {
        auto const it = code.find(hash);
        if (MONAD_LIKELY(it != code.end())) {
            auto &result = it->second;
            return result;
        }
    }
    // block state
    {
        std::shared_lock<Mutex> const lock{block_state.mutex};
        auto const it = block_state.code.find(hash);
        if (MONAD_LIKELY(it != block_state.code.end())) {
            auto const &result = it->second;
            auto const [it, _] = code.try_emplace(hash, result);
            return it->second;
        }
    }
    // database
    auto result = db.read_code(hash);
    {
        std::lock_guard<Mutex> const lock{block_state.mutex};
        auto const [it, inserted] = block_state.code.try_emplace(hash, result);
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second;
        }
    }
    auto const [it, _] = code.try_emplace(hash, result);
    return it->second;
}

template std::optional<Account> &read_account(
    address_t const &, StateDeltas &, BlockState<std::shared_mutex> &, Db &);

template delta_t<bytes32_t> &read_storage(
    address_t const &, uint64_t, bytes32_t const &, StateDeltas &,
    BlockState<std::shared_mutex> &, Db &);

template byte_string &
read_code(bytes32_t const &, Code &, BlockState<std::shared_mutex> &, Db &);

MONAD_NAMESPACE_END
