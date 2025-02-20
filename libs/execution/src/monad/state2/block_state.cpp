#include <monad/config.hpp>
#include <monad/core/account.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/bytes.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/db.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/fmt/state_deltas_fmt.hpp> // NOLINT
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/state.hpp>
#include <monad/vm/evmone/code_analysis.hpp>

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
    , state_(std::make_unique<StateDeltas>())
    , code_(std::make_unique<Code>())
{
}

std::optional<Account> BlockState::read_account(Address const &address)
{
    // block state
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_);
        if (MONAD_LIKELY(state_->find(it, address))) {
            return it->second.account.second;
        }
    }
    // database
    {
        auto const result = db_.read_account(address);
        StateDeltas::const_accessor it{};
        state_->emplace(
            it,
            address,
            StateDelta{.account = {result, result}, .storage = {}});
        return it->second.account.second;
    }
}

bytes32_t BlockState::read_storage(
    Address const &address, Incarnation const incarnation, bytes32_t const &key)
{
    bool read_storage = false;
    // block state
    {
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_);
        MONAD_ASSERT(state_->find(it, address));
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
        auto const &orig_account = it->second.account.first;
        if (orig_account && incarnation == orig_account->incarnation) {
            read_storage = true;
        }
    }
    // database
    {
        auto const result = read_storage
                                ? db_.read_storage(address, incarnation, key)
                                : bytes32_t{};
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        auto const &account = it->second.account.second;
        if (!account || incarnation != account->incarnation) {
            return result;
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
        MONAD_ASSERT(code_);
        if (MONAD_LIKELY(code_->find(it, code_hash))) {
            return it->second;
        }
    }
    // database
    {
        auto const result = db_.read_code(code_hash);
        MONAD_ASSERT(result);
        MONAD_ASSERT(
            code_hash == NULL_HASH || !result->executable_code().empty());
        Code::const_accessor it{};
        code_->emplace(it, code_hash, result);
        return it->second;
    }
}

bool BlockState::can_merge(State &state) const
{
    MONAD_ASSERT(state_);
    for (auto &[address, account_state] : state.original_) {
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_->find(it, address));
        auto const &actual = it->second.account.second;
        if ((account != actual) &&
            !fix_account_mismatch(state, address, account_state, actual)) {
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

    for (auto const &[address, stack] : state.current_) {
        MONAD_ASSERT(stack.size() == 1);
        MONAD_ASSERT(stack.version() == 0);
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        if (account.has_value()) {
            code_hashes.insert(account.value().code_hash);
        }
    }

    MONAD_ASSERT(code_);
    for (auto const &code_hash : code_hashes) {
        auto const it = state.code_.find(code_hash);
        if (it == state.code_.end()) {
            continue;
        }
        code_->emplace(code_hash, it->second); // TODO try_emplace
    }

    MONAD_ASSERT(state_);
    for (auto const &[address, stack] : state.current_) {
        auto const &account_state = stack.recent();
        auto const &account = account_state.account_;
        auto const &storage = account_state.storage_;
        StateDeltas::accessor it{};
        MONAD_ASSERT(state_->find(it, address));
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

void BlockState::commit(
    MonadConsensusBlockHeader const &consensus_header,
    std::vector<Receipt> const &receipts,
    std::vector<std::vector<CallFrame>> const &call_frames,
    std::vector<Address> const &senders,
    std::vector<Transaction> const &transactions,
    std::vector<BlockHeader> const &ommers,
    std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    db_.commit(
        std::move(state_),
        std::move(code_),
        consensus_header,
        receipts,
        call_frames,
        senders,
        transactions,
        ommers,
        withdrawals);
}

void BlockState::log_debug()
{
    MONAD_ASSERT(state_);
    MONAD_ASSERT(code_);
    LOG_DEBUG("State Deltas: {}", *state_);
    LOG_DEBUG("Code Deltas: {}", *code_);
}

bool BlockState::fix_account_mismatch(
    State &state, Address const &address, AccountState &original_state,
    std::optional<Account> const &actual) const
{
    auto &original = original_state.account_;
    if (is_dead(original)) {
        return false;
    }
    if (is_dead(actual)) {
        return false;
    }
    if (original->code_hash != actual->code_hash) {
        return false;
    }
    if (original->incarnation != actual->incarnation) {
        return false;
    }
    bool const nonce_mismatch = original->nonce != actual->nonce;
    if (nonce_mismatch) {
        if (!state.relaxed_validation()) {
            return false;
        }
        if (original_state.validate_exact_nonce()) {
            return false;
        }
    }
    bool const balance_mismatch = original->balance != actual->balance;
    if (balance_mismatch) {
        if (!state.relaxed_validation()) {
            return false;
        }
        if (original_state.validate_exact_balance()) {
            return false;
        }
        if (actual->balance < original_state.min_balance()) {
            return false;
        }
    }
    MONAD_DEBUG_ASSERT(nonce_mismatch || balance_mismatch);
    auto it = state.current_.find(address);
    if (it != state.current_.end()) {
        MONAD_ASSERT(it->second.size() == 1);
        auto &local_state = it->second.recent();
        auto &local = local_state.account_;
        if (nonce_mismatch) {
            MONAD_ASSERT(original->nonce < actual->nonce);
            auto const diff = actual->nonce - original->nonce;
            local->nonce += diff;
        }
        if (balance_mismatch) {
            if (original->balance > actual->balance) {
                auto const diff = original->balance - actual->balance;
                MONAD_ASSERT(local->balance >= diff);
                local->balance -= diff;
            }
            else {
                auto const diff = actual->balance - original->balance;
                local->balance += diff;
            }
        }
    }
    if (nonce_mismatch) {
        original->nonce = actual->nonce;
    }
    if (balance_mismatch) {
        original->balance = actual->balance;
    }
    return true;
}

MONAD_NAMESPACE_END
