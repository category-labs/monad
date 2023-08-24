#pragma once

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/ethereum/fork_traits.hpp>

#include <monad/logging/monad_log.hpp>

#include <chrono>
#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TExecution>
struct AllTxnBlockProcessor
{
    template <class TState, class TTraits, class TFiberData>
    [[nodiscard]] std::vector<Receipt> execute(TState &s, Block &b)
    {
        auto *block_logger = log::logger_t::get_logger("block_logger");
        auto const start_time = std::chrono::steady_clock::now();
        MONAD_LOG_INFO(
            block_logger,
            "Start executing Block {}, with {} transactions",
            b.header.number,
            b.transactions.size());
        MONAD_LOG_DEBUG(block_logger, "BlockHeader Fields: {}", b.header);

        TTraits::transfer_balance_dao(s, b.header.number);

        std::vector<TFiberData> data{};
        std::vector<typename TExecution::fiber_t> fibers{};

        data.reserve(b.transactions.size());
        fibers.reserve(b.transactions.size());

        unsigned int i = 0;
        for (auto &txn : b.transactions) {
            txn.from = recover_sender(txn);
            data.push_back({s, txn, b.header, i});
            fibers.emplace_back(data.back());
            ++i;
        }
        TExecution::yield();

        std::vector<Receipt> r{};
        r.reserve(b.transactions.size());
        for (auto &fiber : fibers) {
            fiber.join();
        }
        for (auto &d : data) {
            r.push_back(d.get_receipt());
        }

        TTraits::process_withdrawal(s, b.withdrawals);

        if (b.header.number != 0u) {
            TTraits::apply_block_award(s, b);
        }

        auto const finished_time = std::chrono::steady_clock::now();
        auto const elapsed_ms =
            std::chrono::duration_cast<std::chrono::milliseconds>(
                finished_time - start_time);
        MONAD_LOG_INFO(
            block_logger,
            "Finish executing Block {}, time elapsed = {}",
            b.header.number,
            elapsed_ms);
        MONAD_LOG_DEBUG(block_logger, "Receipts: {}", r);

        return r;
    }
};

MONAD_EXECUTION_NAMESPACE_END
