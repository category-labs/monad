#pragma once

#include <monad/db/block_db.hpp>
#include <monad/db/state_db.hpp>
#include <monad/execution/block_processor_interface.hpp>
#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/transaction_processor_data.hpp>
#include <monad/trie/state_trie_interface.hpp>

#include <filesystem>
#include <iostream>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <
    class TState, class TBlockDb, class TBlockProcessor, class TStateTrie,
    class TExecution>
class ReplayBlock final
{
public:
    enum class Status
    {
        END_OF_BLOCKDB, // success
        COMPLETE, // success
        START_BLOCK_NUMBER_OUTSIDE_DB,
        INVALID_END_BLOCK_NUMBER,
        ERROR // other error
    };

    struct Result
    {
        Status status;
        block_num_t finished_block_number;
    };

    template <concepts::fork_traits<TState> TTraits>
    [[nodiscard]] Result run_fork(
        TState &state, TBlockDb const &block_db, TStateTrie &state_trie,
        Block &block, block_num_t curr_block_number,
        std::optional<block_num_t> until_block_number = std::nullopt)
    {
        using fiber_data_t = execution::TransactionProcessorFiberData<
            TState,
            TTraits,
            execution::TransactionProcessor<TState, TTraits>,
            execution::Evm<TState, TTraits>,
            TExecution>;
        auto loop_until_block_number = loop_until<TTraits>(until_block_number);
        for (; curr_block_number < loop_until_block_number;
             ++curr_block_number) {

            if (!block_db.get(curr_block_number, block)) {
                return Result{Status::END_OF_BLOCKDB, curr_block_number - 1u};
            }

            TBlockProcessor block_processor{};
            [[maybe_unused]] auto receipts =
                block_processor.template execute<TTraits, fiber_data_t>(
                    block, state);

            state_trie.incremental_update(state);
            state.commit();
        }

        if (!until_block_number.has_value() ||
            until_block_number.value() > curr_block_number) {
            return run_fork<typename TTraits::next_fork_t>(
                state,
                block_db,
                state_trie,
                block,
                curr_block_number,
                until_block_number);
        }
        else {
            return Result{Status::COMPLETE, curr_block_number - 1u};
        }
    }

    [[nodiscard]] Result
    run(TState &state, TBlockDb const &block_db, block_num_t start_block_number,
        std::optional<block_num_t> until_block_number = std::nullopt)
    {
        TStateTrie state_trie{};
        Block block{};

        // invalid input
        if (until_block_number.has_value() &&
            (until_block_number <= start_block_number)) {
            return Result{Status::INVALID_END_BLOCK_NUMBER, 0u};
        }

        if (!block_db.get(start_block_number, block)) {
            return Result{Status::START_BLOCK_NUMBER_OUTSIDE_DB, 0u};
        }

        using fork_function_t = Result (ReplayBlock::*)(
            TState &,
            TBlockDb const &,
            TStateTrie &,
            Block &,
            block_num_t,
            std::optional<block_num_t>);

        fork_function_t fork_functions[] = {
            &ReplayBlock::run_fork<fork_traits::frontier>,
            &ReplayBlock::run_fork<fork_traits::homestead>,
            &ReplayBlock::run_fork<fork_traits::spurious_dragon>,
            &ReplayBlock::run_fork<fork_traits::byzantium>,
            &ReplayBlock::run_fork<fork_traits::istanbul>,
            &ReplayBlock::run_fork<fork_traits::berlin>,
            &ReplayBlock::run_fork<fork_traits::london>};

        block_num_t fork_blocks[] = {
            fork_traits::frontier::last_block_number,
            fork_traits::homestead::last_block_number,
            fork_traits::spurious_dragon::last_block_number,
            fork_traits::byzantium::last_block_number,
            fork_traits::istanbul::last_block_number,
            fork_traits::berlin::last_block_number,
            fork_traits::london::last_block_number};

        uint64_t num_forks = sizeof(fork_functions) / sizeof(fork_function_t);

        for (auto i = 0u; i < num_forks; i++) {
            if (start_block_number <= fork_blocks[i]) {
                return (this->*fork_functions[i])(
                    state,
                    block_db,
                    state_trie,
                    block,
                    start_block_number,
                    until_block_number);
            }
        }

        return Result{Status::ERROR, 0u};
    }

    template <concepts::fork_traits<TState> TTraits>
    [[nodiscard]] constexpr block_num_t
    loop_until(std::optional<block_num_t> block_until)
    {
        if (!block_until.has_value()) {
            return TTraits::last_block_number + 1u;
        }
        else {
            return std::min(
                block_until.value(),
                static_cast<uint64_t>(TTraits::last_block_number + 1u));
        }
    }
};

MONAD_EXECUTION_NAMESPACE_END