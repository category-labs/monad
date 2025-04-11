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

private:
    bool fix_account_mismatch(
        State &state, Address const &address, AccountState &original_state,
        std::optional<Account> const &actual) const;
};

MONAD_NAMESPACE_END
