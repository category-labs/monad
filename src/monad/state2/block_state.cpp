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
        StateDeltas::const_accessor it{};
        if (MONAD_LIKELY(state_.find(it, address))) {
            return it->second.account.second;
        }
    }
    // database
    {
        auto const result = db_.read_account(address);
        StateDeltas::const_accessor it{};
        state_.emplace(
            it,
            address,
            StateDelta{.account = {result, result}, .storage = {}});
        return it->second.account.second;
    }
}

bytes32_t BlockState::read_storage(
    Address const &address, uint64_t const incarnation, bytes32_t const &key)
{
    // block state
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        auto const &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            if (MONAD_LIKELY(storage.find(it2, key))) {
                return it2->second.second;
            }
        }
    }
    // database
    {
        auto const result =
            incarnation == 0 ? db_.read_storage(address, key) : bytes32_t{};
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        auto &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            storage.emplace(it2, key, std::make_pair(result, result));
            return it2->second.second;
        }
    }
}

byte_string BlockState::read_code(bytes32_t const &code_hash)
{
    // block state
    {
        Code::const_accessor it{};
        if (MONAD_LIKELY(code_.find(it, code_hash))) {
            return it->second;
        }
    }
    // database
    {
        auto const result = db_.read_code(code_hash);
        MONAD_ASSERT(code_hash == NULL_HASH || !result.empty());
        Code::const_accessor it{};
        code_.emplace(it, code_hash, result);
        return it->second;
    }
}

bool BlockState::can_merge(State const &state)
{
    for (auto it = state.original_.begin(); it != state.original_.end(); ++it) {
        auto const &address = it->first;
        auto const &account_state = it->second;
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::const_accessor it2{};
        MONAD_ASSERT(state_.find(it2, address));
        if (account != it2->second.account.second) {
            return false;
        }
        // TODO account.has_value()???
        for (auto it3 = storage.cbegin(); it3 != storage.cend(); ++it3) {
            StorageDeltas::const_accessor it4{};
            MONAD_ASSERT(it2->second.storage.find(it4, it3->first));
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
        auto const &stack = it->second;
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack[0].first == 0);
        auto const &account_state = stack[0].second;
        auto const &account = account_state.account_;
        if (account.has_value()) {
            code_hashes.insert(account.value().code_hash);
        }
    }

    for (auto const &code_hash : code_hashes) {
        auto const it = state.code_.find(code_hash);
        if (it == state.code_.end()) {
            continue;
        }
        code_.emplace(code_hash, it->second); // TODO try_emplace
    }

    for (auto it = state.state_.begin(); it != state.state_.end(); ++it) {
        auto const &address = it->first;
        auto const &stack = it->second;
        auto const &account_state = stack[0].second;
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::accessor it2{};
        MONAD_ASSERT(state_.find(it2, address));
        it2->second.account.second = account;
        if (account.has_value()) {
            for (auto it3 = storage.begin(); it3 != storage.end(); ++it3) {
                StorageDeltas::accessor it4{};
                MONAD_ASSERT(it2->second.storage.find(it4, it3->first));
                it4->second.second = it3->second;
            }
        }
        else {
            it2->second.storage.clear();
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
