#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/cpu_relax.h>
#include <monad/core/exec_event.hpp>
#include <monad/core/fmt/transaction_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/core/receipt.hpp>
#include <monad/core/result.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/withdrawal.hpp>
#include <monad/event/event_types.h>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/block_reward.hpp>
#include <monad/execution/ethereum/dao.hpp>
#include <monad/execution/execute_block.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/explicit_evmc_revision.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/trace/event_trace.hpp>
#include <monad/execution/validate_block.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>

#include <evmc/evmc.h>
#include <sys/uio.h>

#include <intx/intx.hpp>

#include <boost/fiber/fss.hpp>
#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <memory>
#include <optional>
#include <utility>
#include <vector>

// Will remain nullptr unless the frontend configure it
monad_event_recorder *monad::g_monad_execution_recorder;

MONAD_NAMESPACE_BEGIN

static boost::fibers::fiber_specific_ptr<uint32_t> g_fss_txn_num;

extern "C" uint32_t monad_event_get_txn_id()
{
    return boost::fibers::context::active()
               ? g_fss_txn_num.get() != nullptr ? *g_fss_txn_num + 1 : 0
               : 0;
}

static std::span<iovec const> init_txn_header_iovec(
    Transaction const &txn, std::optional<Address> const &opt_sender,
    iovec (&iov)[2])
{
    size_t iovlen = 1;
    auto *const header = static_cast<monad_event_txn_header *>(iov[0].iov_base);
    header->tx_hash = to_bytes(keccak256(rlp::encode_transaction(txn)));
    header->nonce = txn.nonce;
    header->gas_limit = txn.gas_limit;
    header->max_fee_per_gas = to_bytes(txn.max_fee_per_gas);
    header->max_priority_fee_per_gas = to_bytes(txn.max_priority_fee_per_gas);
    header->value = to_bytes(txn.value);
    header->from = opt_sender ? *opt_sender : Address{};
    header->to = txn.to ? *txn.to : Address{};
    header->txn_type = static_cast<uint8_t>(txn.type);
    header->r = to_bytes(txn.sc.r);
    header->s = to_bytes(txn.sc.s);
    header->y_parity = txn.sc.odd_y_parity ? 1 : 0;
    header->chain_id = to_bytes(txn.sc.chain_id.value_or(0));
    header->data_length = static_cast<uint32_t>(size(txn.data));
    if (header->data_length > 0) {
        ++iovlen;
        iov[1].iov_base = (void *)data(txn.data);
        iov[1].iov_len = header->data_length;
    }
    return {iov, iovlen};
}

static void record_txn_exec_result_events(Result<ExecutionResult> const &r)
{
    if (r.has_error()) {
        // Create a reference error so we can extract its domain with
        // `ref_txn_error.domain()`, for the purpose of checking if the
        // r.error() domain is a TransactionError
        static Result<ExecutionResult>::error_type const ref_txn_error =
            TransactionError::InsufficientBalance;
        static auto const &txn_err_domain = ref_txn_error.domain();
        auto const &error_domain = r.error().domain();
        auto const error_value = r.error().value();
        if (error_domain == txn_err_domain) {
            record_exec_event(MONAD_EVENT_TXN_REJECT, error_value);
        }
        else {
            monad_event_txn_exec_error ee;
            ee.domain_id = error_domain.id();
            ee.status_code = error_value;
            record_exec_event(MONAD_EVENT_TXN_EXEC_ERROR, ee);
        }
        return;
    }

    auto const &receipt = r.value().receipt;
    for (auto const &log : receipt.logs) {
        iovec iov[3];
        monad_event_txn_log log_event;

        log_event.address = log.address;
        log_event.topic_count = static_cast<uint8_t>(size(log.topics));
        log_event.data_length = static_cast<uint32_t>(size(log.data));
        iov[0] = {.iov_base = &log_event, .iov_len = sizeof log_event};
        iov[1] = {
            .iov_base = const_cast<bytes32_t *>(log.topics.data()),
            .iov_len = log_event.topic_count * sizeof(bytes32_t)};
        iov[2] = {
            .iov_base = const_cast<uint8_t *>(log.data.data()),
            .iov_len = log_event.data_length};
        record_exec_event_iov(MONAD_EVENT_TXN_LOG, iov);
    }
    monad_event_txn_receipt const receipt_event = {
        .status = receipt.status, .gas_used = receipt.gas_used};
    record_exec_event(MONAD_EVENT_TXN_RECEIPT, receipt_event);
}

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

inline void set_beacon_root(BlockState &block_state, Block &block)
{
    constexpr auto BEACON_ROOTS_ADDRESS{
        0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02_address};
    constexpr uint256_t HISTORY_BUFFER_LENGTH{8191};

    State state{block_state, Incarnation{block.header.number, 0}};
    if (state.account_exists(BEACON_ROOTS_ADDRESS)) {
        uint256_t timestamp{block.header.timestamp};
        bytes32_t k1{
            to_bytes(to_big_endian(timestamp % HISTORY_BUFFER_LENGTH))};
        bytes32_t k2{to_bytes(to_big_endian(
            timestamp % HISTORY_BUFFER_LENGTH + HISTORY_BUFFER_LENGTH))};
        state.set_storage(
            BEACON_ROOTS_ADDRESS, k1, to_bytes(to_big_endian(timestamp)));
        state.set_storage(
            BEACON_ROOTS_ADDRESS,
            k2,
            block.header.parent_beacon_block_root.value());

        MONAD_ASSERT(block_state.can_merge(state));
        block_state.merge(state);
    }
}

template <evmc_revision rev>
Result<std::vector<ExecutionResult>> execute_block(
    Chain const &chain, Block &block, BlockState &block_state,
    BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    TRACE_BLOCK_EVENT(StartBlock);

    if constexpr (rev >= EVMC_CANCUN) {
        set_beacon_root(block_state, block);
    }

    if constexpr (rev == EVMC_HOMESTEAD) {
        if (MONAD_UNLIKELY(block.header.number == dao::dao_block_number)) {
            transfer_balance_dao(
                block_state, Incarnation{block.header.number, 0});
        }
    }

    std::shared_ptr<std::optional<Address>[]> const senders{
        new std::optional<Address>[block.transactions.size()]};

    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[block.transactions.size()]};

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i = i,
             senders = senders,
             promises = promises,
             &transaction = block.transactions[i]] {
                senders[i] = recover_sender(transaction);
                promises[i].set_value();
                monad_event_txn_header txn_header;
                iovec iov[2] = {
                    {.iov_base = &txn_header, .iov_len = sizeof txn_header},
                };
                g_fss_txn_num.reset(new uint32_t{i});
                record_exec_event_iov(
                    MONAD_EVENT_TXN_START,
                    init_txn_header_iovec(transaction, senders[i], iov));
                g_fss_txn_num.release();
            });
    }

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        promises[i].get_future().wait();
    }

    std::shared_ptr<std::optional<Result<ExecutionResult>>[]> const results{
        new std::optional<Result<ExecutionResult>>[block.transactions.size()]};

    promises.reset(
        new boost::fibers::promise<void>[block.transactions.size() + 1]);
    promises[0].set_value();

    std::atomic<size_t> tx_exec_finished = 0;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [&chain = chain,
             i = i,
             results = results,
             promises = promises,
             &transaction = block.transactions[i],
             &sender = senders[i],
             &header = block.header,
             &block_hash_buffer = block_hash_buffer,
             &block_state,
             &tx_exec_finished] {
                g_fss_txn_num.reset(new uint32_t{i});
                results[i] = execute<rev>(
                    chain,
                    i,
                    transaction,
                    sender,
                    header,
                    block_hash_buffer,
                    block_state,
                    promises[i]);
                promises[i + 1].set_value();
                record_txn_exec_result_events(*results[i]);
                g_fss_txn_num.release();
                tx_exec_finished.fetch_add(1, std::memory_order::relaxed);
            });
    }

    auto const last = static_cast<std::ptrdiff_t>(block.transactions.size());
    promises[last].get_future().wait();

    // All transactions have released their merge-order synchronization
    // primitive (promises[i + 1]) but some stragglers could still be running
    // post-execution code that occurs immediately after that, e.g.
    // `record_txn_exec_result_events`. This waits for everything to finish
    // so that it's safe to assume we're the only ones using `results`.
    while (tx_exec_finished.load() < block.transactions.size()) {
        cpu_relax();
    }

    std::vector<ExecutionResult> retvals;
    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        MONAD_ASSERT(results[i].has_value());
        if (MONAD_UNLIKELY(results[i].value().has_error())) {
            LOG_ERROR(
                "tx {} {} validation failed: {}",
                i,
                block.transactions[i],
                results[i].value().assume_error().message().c_str());
        }
        BOOST_OUTCOME_TRY(auto retval, std::move(results[i].value()));
        retvals.push_back(std::move(retval));
    }

    // YP eq. 22
    uint64_t cumulative_gas_used = 0;
    for (auto &[receipt, _, call_frame] : retvals) {
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

    return retvals;
}

EXPLICIT_EVMC_REVISION(execute_block);

Result<std::vector<ExecutionResult>> execute_block(
    Chain const &chain, evmc_revision const rev, Block &block,
    BlockState &block_state, BlockHashBuffer const &block_hash_buffer,
    fiber::PriorityPool &priority_pool)
{
    SWITCH_EVMC_REVISION(
        execute_block,
        chain,
        block,
        block_state,
        block_hash_buffer,
        priority_pool);
    MONAD_ASSERT(false);
}

MONAD_NAMESPACE_END
