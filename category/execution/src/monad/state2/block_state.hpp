#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/db.hpp>
#include <monad/execution/trace/call_tracer.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/types/incarnation.hpp>
#include <monad/vm/vm.hpp>

#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

class BlockState final
{
    Db &db_;
    vm::VM &vm_;
    std::unique_ptr<StateDeltas> state_;
    Code code_;

public:
    BlockState(Db &, vm::VM &);

    vm::VM &vm()
    {
        return vm_;
    }

    std::optional<Account> read_account(Address const &);

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &key);

    vm::SharedVarcode read_code(bytes32_t const &);

    bool can_merge(State const &);

    void merge(State const &);

    void commit(
        bytes32_t const &block_id, MonadConsensusBlockHeader const &,
        std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const & = {});

    void log_debug();
};

MONAD_NAMESPACE_END
