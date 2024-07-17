#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/fmt/transaction_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

// EIP-4895
constexpr void process_withdrawal(
    State &state, std::optional<std::vector<Withdrawal>> const &withdrawals)
{
    if (withdrawals.has_value()) {
        for (auto const &withdrawal : withdrawals.value()) {
            state.add_to_balance(
                withdrawal.recipient,
                uint256_t{withdrawal.amount} * uint256_t{1'000'000'000u});
        }
    }
}

inline void
transfer_balance_dao(BlockState &block_state, Incarnation const incarnation)
{
    State state{block_state, incarnation};

    for (auto const &addr : dao::child_accounts) {
        auto const balance = intx::be::load<uint256_t>(state.get_balance(addr));
        state.add_to_balance(dao::withdraw_account, balance);
        state.subtract_from_balance(addr, balance);
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);
}

template <evmc_revision rev>
Result<std::vector<Receipt>> execute_block(
    Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    TRACE_BLOCK_EVENT(StartBlock);

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(
                block_state, Incarnation{block.header.number, 0});
        }
    }

    std::shared_ptr<std::optional<Result<Receipt>>[]> const results{
        new std::optional<Result<Receipt>>[block.transactions.size()]};

    std::shared_ptr<boost::fibers::promise<void>[]> const promises{
        new boost::fibers::promise<void>[block.transactions.size() + 1]};
    promises[0].set_value();

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i = i,
             results = results,
             promises = promises,
             &transaction = block.transactions[i],
             &header = block.header,
             &block_hash_buffer = block_hash_buffer,
             &block_state] {
                results[i] = execute<rev>(
                    i,
                    transaction,
                    header,
                    block_hash_buffer,
                    block_state,
                    promises[i]);
                promises[i + 1].set_value();
            });
    }

    auto const last = static_cast<std::ptrdiff_t>(block.transactions.size());
    promises[last].get_future().wait();

    std::vector<Receipt> receipts;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_UNLIKELY(results[i].value().has_error())) {
            LOG_ERROR(
                "tx {} validation failed: {}",
                i,
                results[i].value().assume_error().message().c_str());
            LOG_ERROR("failed tx: {}", block.transactions[i]);
        }
        BOOST_OUTCOME_TRY(Receipt receipt, std::move(results[i].value()));
        receipts.push_back(std::move(receipt));
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &receipt : receipts) {
        cumulative_gas_used += receipt.gas_used;
        receipt.gas_used = cumulative_gas_used;
    }

    State state{
        block_state, Incarnation{block.header.number, Incarnation::LAST_TX}};

    if constexpr (rev >= EVMC_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    apply_block_reward<rev>(state, block);

    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }

    MONAD_ASSERT(block_state.can_merge(state));
    block_state.merge(state);

    return receipts;
}

EXPLICIT_EVMC_REVISION(execute_block);

Result<std::vector<Receipt>> execute_block(
    evmc_revision const rev, Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    switch (rev) {
    case EVMC_SHANGHAI:
        return execute_block<EVMC_SHANGHAI>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_PARIS:
        return execute_block<EVMC_PARIS>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_LONDON:
        return execute_block<EVMC_LONDON>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_BERLIN:
        return execute_block<EVMC_BERLIN>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_ISTANBUL:
        return execute_block<EVMC_ISTANBUL>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_PETERSBURG:
    case EVMC_CONSTANTINOPLE:
        return execute_block<EVMC_PETERSBURG>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_BYZANTIUM:
        return execute_block<EVMC_BYZANTIUM>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_SPURIOUS_DRAGON:
        return execute_block<EVMC_SPURIOUS_DRAGON>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_TANGERINE_WHISTLE:
        return execute_block<EVMC_TANGERINE_WHISTLE>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_HOMESTEAD:
        return execute_block<EVMC_HOMESTEAD>(
            block, block_state, block_hash_buffer, priority_pool);
    case EVMC_FRONTIER:
        return execute_block<EVMC_FRONTIER>(
            block, block_state, block_hash_buffer, priority_pool);
    default:
        break;
    }
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
