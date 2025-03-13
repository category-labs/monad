#pragma once

#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/state3/account_state.hpp>
#include <monad/types/incarnation.hpp>
#include <monad/vm/evmone/code_analysis.hpp>

#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

class BlockState final
{
    Db &db_;
    std::unique_ptr<StateDeltas> state_;
    std::unique_ptr<Code> code_;

public:
uint64_t n_retries_{0}, precalc_time_{0}, exec_time_{0};
    BlockState(Db &);

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &key);

    std::shared_ptr<CodeAnalysis> read_code(bytes32_t const &);

    bool can_merge(State &) const;

    void merge(State const &);

    // TODO: remove round_number parameter, retrieve it from header instead once
    // we add the monad fields in BlockHeader
    void commit(
        MonadConsensusBlockHeader const &, std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = {});

    void log_debug();

    uint32_t n_restarts_{0};
    std::optional<Account> try_emplace_account(
        Address const &address, std::optional<Account> const &account)
    {
        StateDeltas::const_accessor it{};
        state_->emplace(
            it,
            address,
            StateDelta{.account = {account, account}, .storage = {}});
        return it->second.account.second;
    }

    bytes32_t try_emplace_storage(
        Address const &address, Incarnation incarnation, bytes32_t const &key,
        bytes32_t const &result)
    {
        StateDeltas::accessor it{};
        bool const found = state_->find(it, address);
        MONAD_ASSERT(found);
        auto const &account = it->second.account.second;
        if (!account || incarnation != account->incarnation) {
            return result;
        }
        auto &storage = it->second.storage;
        StorageDeltas::const_accessor it2{};
        storage.emplace(it2, key, std::make_pair(result, result));
        return it2->second.second;
    }

    template <class Func1, class Func2>
    std::optional<Account>
    read_account(Address const &address, Func1 fn1, Func2 fn2)
    {
        {
            StateDeltas::const_accessor it{};
            if (state_->find(it, address)) {
                return it->second.account.second;
            }
        }
        std::optional<Account> result;
        auto fn3 = [this, fn2, address](std::optional<Account> const &account) {
            try_emplace_account(address, account);
            fn2(account.has_value());
        };
        if (db_.read_account(address, result, fn1, fn3)) {
            return try_emplace_account(address, result);
        }
        else {
            return std::nullopt;
        }
    }

    template <class Func1, class Func2>
    bytes32_t read_storage(
        Address const &address, Incarnation incarnation, bytes32_t const &key,
        Func1 fn1, Func2 fn2)
    {
        bool read_storage = false;
        {
            StateDeltas::const_accessor it{};
            bool const found = state_->find(it, address);
            if (!found) {
                // We must have already guessed (incorrectly) that the
                // account doesn't exist.
                return {};
            }
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
        bytes32_t result;
        bool miss = false;
        if (read_storage) {
            auto fn3 =
                [this, fn2, address, incarnation, key](bytes32_t const &value) {
                    try_emplace_storage(address, incarnation, key, value);
                    fn2(value != bytes32_t{});
                };
            miss =
                !db_.read_storage(address, incarnation, key, result, fn1, fn3);
        }
        else {
            result = bytes32_t{};
        }
        if (miss) {
            return bytes32_t{};
        }
        else {
            return try_emplace_storage(address, incarnation, key, result);
        }
    }

    void add_restarts(uint32_t restarts)
    {
        n_restarts_ += restarts;
    }

    uint32_t num_restarts()
    {
        return n_restarts_;
    }

private:
    bool fix_account_mismatch(
        State &state, Address const &address, AccountState &original_state,
        std::optional<Account> const &actual) const;
};

MONAD_NAMESPACE_END
