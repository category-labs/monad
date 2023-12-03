#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/block_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/transaction.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state2/state.hpp>
#include <monad/state2/state_deltas_fmt.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <quill/detail/LogMacros.h>

#include <boost/outcome/try.hpp>

#include <chrono>
#include <cstdint>
#include <optional>
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

inline void transfer_balance_dao(BlockState &block_state)
{
    State state{block_state};

    for (auto const &addr : dao::child_accounts) {
        auto const balance = intx::be::load<uint256_t>(state.get_balance(addr));
        state.add_to_balance(dao::withdraw_account, balance);
        state.subtract_from_balance(addr, balance);
    }

    MONAD_DEBUG_ASSERT(block_state.can_merge(state.state_));
    block_state.merge(state.state_);
}

constexpr Receipt::Bloom compute_bloom(std::vector<Receipt> const &receipts)
{
    Receipt::Bloom bloom{};
    for (auto const &receipt : receipts) {
        for (unsigned i = 0; i < 256; ++i) {
            bloom[i] |= receipt.bloom[i];
        }
    }

    return bloom;
}

inline void commit(BlockState &block_state)
{
    auto const start_time = std::chrono::steady_clock::now();
    LOG_INFO("{}", "Committing to DB...");

    block_state.commit();

    auto const finished_time = std::chrono::steady_clock::now();
    auto const elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_time - start_time);
    LOG_INFO("Finished committing, time elapsed = {}", elapsed_ms);
}

template <evmc_revision rev>
Result<std::vector<Receipt>>
execute_block(Block &block, Db &db, BlockHashBuffer const &block_hash_buffer)
{
    auto const start_time = std::chrono::steady_clock::now();
    LOG_INFO(
        "Start executing Block {}, with {} transactions",
        block.header.number,
        block.transactions.size());
    LOG_DEBUG("BlockHeader Fields: {}", block.header);

    BlockState block_state{db};
    uint64_t cumulative_gas_used = 0;

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(block_state);
        }
    }

    std::vector<Receipt> receipts{};
    receipts.reserve(block.transactions.size());

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        State state{block_state};

        BOOST_OUTCOME_TRY(
            auto const receipt,
            execute<rev>(
                block.transactions[i], block.header, block_hash_buffer, state));

        LOG_DEBUG("State Deltas: {}", state.state_);
        LOG_DEBUG("Code Deltas: {}", state.code_);

        MONAD_DEBUG_ASSERT(block_state.can_merge(state.state_));
        block_state.merge(state.state_);
        block_state.merge(state.code_);

        cumulative_gas_used += receipt.gas_used;
        receipts.push_back(receipt);
    }

    // YP eq. 33
    if (compute_bloom(receipts) != block.header.logs_bloom) {
        return BlockError::WrongLogsBloom;
    }

    // YP eq. 170
    if (cumulative_gas_used != block.header.gas_used) {
        return BlockError::InvalidGasUsed;
    }

    State state{block_state};
    if constexpr (rev >= EVMC_SHANGHAI) {
        process_withdrawal(state, block.withdrawals);
    }

    apply_block_reward<rev>(block_state, block);

    if constexpr (rev >= EVMC_SPURIOUS_DRAGON) {
        state.destruct_touched_dead();
    }
    MONAD_DEBUG_ASSERT(block_state.can_merge(state.state_));
    block_state.merge(state.state_);

    auto const finished_time = std::chrono::steady_clock::now();
    auto const elapsed_ms =
        std::chrono::duration_cast<std::chrono::milliseconds>(
            finished_time - start_time);
    LOG_INFO(
        "Finish executing Block {}, time elapsed = {}",
        block.header.number,
        elapsed_ms);
    LOG_DEBUG("Receipts: {}", receipts);

    commit(block_state);

    return receipts;
}

EXPLICIT_EVMC_REVISION(execute_block);

MONAD_NAMESPACE_END
