#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/code_analysis.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/fmt/state_deltas_fmt.hpp> // NOLINT
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>

#include <ankerl/unordered_dense.h>

#include <quill/detail/LogMacros.h>

#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

BlockState::BlockState(Db &db)
    : db_{db}
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
        auto const &account = it->second.account.second;
        if (!account || incarnation != account->incarnation) {
            return {};
        }
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
        if (incarnation) {
            return {};
        }
        auto const result = db_.read_storage(address, key);
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        auto const &account = it->second.account.second;
        if (!account || account->incarnation) {
            return {};
        }
        auto &storage = it->second.storage;
        {
            StorageDeltas::const_accessor it2{};
            storage.emplace(it2, key, std::make_pair(result, result));
            return it2->second.second;
        }
    }
}

std::shared_ptr<CodeAnalysis> BlockState::read_code(bytes32_t const &code_hash)
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
        MONAD_ASSERT(result);
        MONAD_ASSERT(
            code_hash == NULL_HASH || !result->executable_code.empty());
        Code::const_accessor it{};
        code_.emplace(it, code_hash, result);
        return it->second;
    }
}

bool BlockState::can_merge(State const &state)
{
    for (auto const &[address, account_state] : state.original_) {
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        if (account != it->second.account.second) {
            return false;
        }
        // TODO account.has_value()???
        for (auto const &[key, value] : storage) {
            StorageDeltas::const_accessor it2{};
            if (it->second.storage.find(it2, key)) {
                if (value != it2->second.second) {
                    return false;
                }
            }
            else {
                if (value) {
                    return false;
                }
            }
        }
    }
    return true;
}

void BlockState::merge(State const &state)
{
    ankerl::unordered_dense::segmented_set<bytes32_t> code_hashes;

    for (auto const &[address, stack] : state.state_) {
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto const &account_state = stack.recent();
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

    for (auto const &[address, stack] : state.state_) {
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_.find(it, address));
        it->second.account.second = account;
        if (account.has_value()) {
            for (auto const &[key, value] : storage) {
                StorageDeltas::accessor it2{};
                if (it->second.storage.find(it2, key)) {
                    it2->second.second = value;
                }
                else {
                    it->second.storage.emplace(
                        key, std::make_pair(bytes32_t{}, value));
                }
            }
        }
        else {
            it->second.storage.clear();
        }
    }
}

void BlockState::commit(std::vector<Receipt> const &receipts)
{
    db_.increment_block_number();
    db_.commit(state_, code_, receipts);
}

void BlockState::log_debug()
{
    LOG_DEBUG("State Deltas: {}", state_);
    LOG_DEBUG("Code Deltas: {}", code_);
}

MONAD_NAMESPACE_END
