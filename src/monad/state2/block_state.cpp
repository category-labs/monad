#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/db/db.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state_deltas.hpp>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db)
    : db_{db}
    , mutex_{}
    , state_{}
    , code_{}
{
}

std::optional<Account> BlockState::read_account(address_t const &address)
{
    // block state
    {
        SharedLock const lock{mutex_};
        auto const it = state_.find(address);
        if (MONAD_LIKELY(it != state_.end())) {
            return it->second.account.second;
        }
    }
    // database
    auto result = db_.read_account(address);
    {
        LockGuard const lock{mutex_};
        auto const [it, inserted] = state_.try_emplace(
            address, StateDelta{.account = {result, result}, .storage = {}});
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second.account.second;
        }
    }
    return result;
}

bytes32_t BlockState::read_storage(
    address_t const &address, uint64_t /*const incarnation*/,
    bytes32_t const &location)
{
    // block state
    {
        SharedLock const lock{mutex_};
        auto const it = state_.find(address);
        MONAD_ASSERT(it != state_.end());
        auto const &storage = it->second.storage;
        {
            auto const it = storage.find(location);
            if (MONAD_LIKELY(it != storage.end())) {
                return it->second.second;
            }
        }
    }
    // database
    auto result = db_.read_storage(address, location);
    {
        LockGuard const lock{mutex_};
        auto const it = state_.find(address);
        MONAD_ASSERT(it != state_.end());
        auto &storage = it->second.storage;
        {
            auto const [it, inserted] =
                storage.try_emplace(location, result, result);
            if (MONAD_UNLIKELY(!inserted)) {
                result = it->second.second;
            }
        }
    }
    return result;
}

byte_string BlockState::read_code(bytes32_t const &hash)
{
    // block state
    {
        SharedLock const lock{mutex_};
        auto const it = code_.find(hash);
        if (MONAD_LIKELY(it != code_.end())) {
            return it->second;
        }
    }
    // database
    auto result = db_.read_code(hash);
    {
        LockGuard const lock{mutex_};
        auto const [it, inserted] = code_.try_emplace(hash, result);
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second;
        }
    }
    return result;
}

bool BlockState::can_merge(StateDeltas const &state)
{
    SharedLock const lock{mutex_};
    return ::monad::can_merge(state_, state);
}

void BlockState::merge(StateDeltas const &state)
{
    LockGuard const lock{mutex_};
    ::monad::merge(state_, state);
}

void BlockState::merge(Code const &code)
{
    LockGuard const lock{mutex_};
    ::monad::merge(code_, code);
}

void BlockState::commit()
{
    SharedLock const lock{mutex_};
    db_.commit(state_, code_);
}

MONAD_NAMESPACE_END
