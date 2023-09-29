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

std::optional<Account> BlockState::read_account(Address const &address)
{
    // block state
    {
        ReadLock const lock{mutex_};
        auto const it = state_.find(address);
        if (MONAD_LIKELY(it != state_.end())) {
            return it->second.account.second;
        }
    }
    // database
    auto result = db_.read_account(address);
    {
        WriteLock const lock{mutex_};
        auto const [it, inserted] = state_.try_emplace(
            address, StateDelta{.account = {result, result}, .storage = {}});
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second.account.second;
        }
    }
    return result;
}

bytes32_t BlockState::read_storage(
    Address const &address, uint64_t const incarnation,
    bytes32_t const &location)
{
    // block state
    {
        ReadLock const lock{mutex_};
        auto const it = state_.find(address);
        MONAD_ASSERT(it != state_.end());
        auto const &storage = it->second.storage;
        {
            auto const it2 = storage.find(location);
            if (MONAD_LIKELY(it2 != storage.end())) {
                return it2->second.second;
            }
        }
    }
    // database
    auto result =
        incarnation == 0 ? db_.read_storage(address, location) : bytes32_t{};
    {
        WriteLock const lock{mutex_};
        auto const it = state_.find(address);
        MONAD_ASSERT(it != state_.end());
        auto &storage = it->second.storage;
        {
            auto const [it2, inserted] =
                storage.try_emplace(location, result, result);
            if (MONAD_UNLIKELY(!inserted)) {
                result = it2->second.second;
            }
        }
    }
    return result;
}

byte_string BlockState::read_code(bytes32_t const &hash)
{
    // block state
    {
        ReadLock const lock{mutex_};
        auto const it = code_.find(hash);
        if (MONAD_LIKELY(it != code_.end())) {
            return it->second;
        }
    }
    // database
    auto result = db_.read_code(hash);
    {
        WriteLock const lock{mutex_};
        auto const [it, inserted] = code_.try_emplace(hash, result);
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second;
        }
    }
    return result;
}

bool BlockState::can_merge(StateDeltas const &state)
{
    ReadLock const lock{mutex_};
    return ::monad::can_merge(state_, state);
}

void BlockState::merge(StateDeltas const &state)
{
    WriteLock const lock{mutex_};
    ::monad::merge(state_, state);
}

void BlockState::merge(Code const &code)
{
    WriteLock const lock{mutex_};
    ::monad::merge(code_, code);
}

void BlockState::commit()
{
    ReadLock const lock{mutex_};
    db_.commit(state_, code_);
}

MONAD_NAMESPACE_END
