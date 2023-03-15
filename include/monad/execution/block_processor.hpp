#pragma once

#include <monad/core/block.hpp>
#include <monad/core/receipt.hpp>
#include <monad/core/transaction.hpp>

#include <monad/execution/config.hpp>

#include <vector>

MONAD_EXECUTION_NAMESPACE_BEGIN

template <class TExecution>
struct AllTxnBlockProcessor
{
    template <class TState, class TFiberData>
    std::vector<Receipt> execute(TState &s, Block const &b)
    {
        std::vector<TFiberData> data{};
        std::vector<typename TExecution::fiber_t> fibers{};

        data.reserve(b.transactions.size());
        fibers.reserve(b.transactions.size());

        int i = 0;
        for (auto const &txn : b.transactions) {
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
        return r;
    }
};

MONAD_EXECUTION_NAMESPACE_END
