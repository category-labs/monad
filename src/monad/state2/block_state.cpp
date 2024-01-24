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
#include <monad/state2/state_deltas_fmt.hpp>
#include <monad/state3/state.hpp>

#include <quill/detail/LogMacros.h>

#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db)
    : db_{db}
    , state_{}
    , code_{}
{
}

std::optional<Account> BlockState::read_account(Address const &address)
{
    // block state
    {
        auto const it = state_.find(address);
        if (MONAD_LIKELY(it != state_.end())) {
            return it->second.account.second;
        }
    }
    // database
    auto result = db_.read_account(address);
    {
        auto const [it, inserted] = state_.emplace(
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
        auto const it = state_.find(address);
        MONAD_ASSERT(it != state_.end());
        auto &storage = it->second.storage;
        {
            auto const [it2, inserted] =
                storage.emplace(location, std::make_pair(result, result));
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
        auto const it = code_.find(hash);
        if (MONAD_LIKELY(it != code_.end())) {
            return it->second;
        }
    }
    // database
    auto result = db_.read_code(hash);
    {
        auto const [it, inserted] = code_.emplace(hash, result);
        if (MONAD_UNLIKELY(!inserted)) {
            result = it->second;
        }
    }
    return result;
}

bool BlockState::can_merge(State const &state)
{
    for (auto it = state.original_.begin(); it != state.original_.end(); ++it) {
        auto const &address = it->first;
        auto const &account_state = it->second;
        auto const it2 = state_.find(address);
        MONAD_ASSERT(it2 != state_.end());
        if (account_state.account_ != it2->second.account.second) {
            return false;
        }
        for (auto it3 = account_state.storage_.begin();
             it3 != account_state.storage_.end();
             ++it3) {
            auto const it4 = it2->second.storage.find(it3->first);
            MONAD_ASSERT(it4 != it2->second.storage.end());
            if (it3->second != it4->second.second) {
                return false;
            }
        }
    }
    return true;
}

void BlockState::merge(State const &state)
{
    ankerl::unordered_dense::segmented_set<bytes32_t> code_hashes;

    for (auto it = state.state_.begin(); it != state.state_.end(); ++it) {
        auto const &address = it->first;
        auto const &stack = it->second;
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack[0].first == 0);
        auto const &account_state = stack[0].second;
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        auto const it2 = state_.find(address);
        MONAD_ASSERT(it2 != state_.end());
        it2->second.account.second = account;
        if (account.has_value()) {
            for (auto it3 = storage.begin(); it3 != storage.end(); ++it3) {
                auto const it4 = it2->second.storage.find(it3->first);
                MONAD_ASSERT(it4 != it2->second.storage.end());
                it4->second.second = it3->second;
            }
            code_hashes.insert(account.value().code_hash);
        }
        else {
            it2->second.storage.clear();
        }
    }

    for (auto const &code_hash : code_hashes) {
        auto const it = state.code_.find(code_hash);
        if (it == state.code_.end()) {
            continue;
        }
        auto const it2 = code_.find(code_hash);
        if (it2 != code_.end()) {
            if (it2->second.empty()) {
                it2->second = it->second;
            }
        }
        else {
            code_[code_hash] = it->second;
        }
    }
}

void BlockState::commit()
{
    db_.commit(state_, code_);
}

void BlockState::log_debug()
{
    LOG_DEBUG("State Deltas: {}", state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
