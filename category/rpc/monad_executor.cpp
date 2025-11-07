// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <category/rpc/monad_executor.h>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/lru/static_lru_cache.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/trace/tracer_config.h>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>
#include <boost/scope_exit.hpp>

#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <format>
#include <map>
#include <memory>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

#include <string.h>

#include <ankerl/unordered_dense.h>
#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>
#include <intx/intx.hpp>
#include <nlohmann/json_fwd.hpp>
#include <quill/Quill.h>

using namespace monad;
using namespace monad::vm;

struct monad_state_override
{
    struct monad_state_override_object
    {
        std::optional<byte_string> balance{std::nullopt};
        std::optional<uint64_t> nonce{std::nullopt};
        std::optional<byte_string> code{std::nullopt};
        std::map<byte_string, byte_string> state{};
        std::map<byte_string, byte_string> state_diff{};
    };

    std::map<byte_string, monad_state_override_object> override_sets;
};

namespace
{
    // eth call on latest uses eip-2935. historical eth calls use this class,
    // which lazily loads the block header from the DB and computes BLOCKHASH.
    // historical can always query from the finalized prefix.
    //
    // A thread-safe LRU is not needed. Each submitted call to the executor pool
    // creates its own LazyBlockHash instance.
    class LazyBlockHash : public BlockHashBuffer
    {
        using BlockHashBuffer::N;

        mpt::RODb const &db_;
        uint64_t const n_;
        using Cache = static_lru_cache<uint64_t, bytes32_t>;
        mutable Cache blockhash_cache_;

    public:
        LazyBlockHash(mpt::RODb const &db, uint64_t const n)
            : db_{db}
            , n_{n}
            , blockhash_cache_{N}
        {
        }

        ~LazyBlockHash() override = default;

        uint64_t n() const override
        {
            return n_;
        }

        bytes32_t const &get(uint64_t const n) const override
        {
            MONAD_ASSERT(n < n_ && n + N >= n_);
            if (Cache::ConstAccessor acc; blockhash_cache_.find(acc, n)) {
                return acc->second->val;
            }

            auto const cursor_res = db_.find(
                mpt::concat(
                    FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
                n);
            MONAD_ASSERT_THROW(
                !cursor_res.has_error(), "blockhash: error querying DB");
            bytes32_t const blockhash =
                to_bytes(keccak256(cursor_res.value().node->value()));
            auto const res = blockhash_cache_.insert(n, blockhash);
            return res.first->second->val;
        }
    };

    char const *const UNEXPECTED_EXCEPTION_ERR_MSG = "unexpected error";
    char const *const EXCEED_QUEUE_SIZE_ERR_MSG =
        "failure to submit eth_call to thread pool: queue size exceeded";
    char const *const TIMEOUT_ERR_MSG =
        "failure to execute eth_call: queuing time exceeded timeout threshold";
    char const *const PRESTATE_TRACER_SUPPORT_ERR_MSG =
        "only the prestate tracer and the statediff "
        "tracer are supported";
    char const *const CANNOT_TRACE_GENESIS_ERR_MSG =
        "cannot trace genesis block";
    char const *const RECOVER_SENDER_ERR_MSG = "failed to recover sender";
    char const *const TRANSACTIONS_CONTEXT_ERR_MSG =
        "failed to recover the transactions context";
    char const *const PARENT_TRANSACTIONS_CONTEXT_ERR_MSG =
        "failed to recover the parent transactions context";
    char const *const GRANDPARENT_TRANSACTIONS_CONTEXT_ERR_MSG =
        "failed to recover the grandparent transactions context";
    char const *const TRANSACTION_OUT_OF_BOUNDS_ERR_MSG =
        "transaction out of bounds";
    using StateOverrideObj = monad_state_override::monad_state_override_object;

    template <Traits traits>
    Result<evmc::Result> eth_call_impl(
        Chain const &chain, Transaction const &txn, BlockHeader const &header,
        uint64_t const block_number, bytes32_t const &block_id,
        Address const &sender,
        std::vector<std::optional<Address>> const &authorities, TrieRODb &tdb,
        vm::VM &vm, BlockHashBuffer const &buffer,
        monad_state_override const &state_overrides,
        CallTracerBase &call_tracer, trace::StateTracer state_tracer)
    {
        Transaction enriched_txn{txn};

        // static_validate_transaction checks sender's signature and chain_id.
        // However, eth_call doesn't have signature (it can be simulated from
        // any account). Solving this issue by setting chain_id and signature to
        // complied values
        enriched_txn.sc.chain_id = chain.get_chain_id();
        enriched_txn.sc.r = 1;
        enriched_txn.sc.s = 1;

        BOOST_OUTCOME_TRY(static_validate_transaction<traits>(
            enriched_txn,
            header.base_fee_per_gas,
            header.excess_blob_gas,
            chain.get_chain_id()));

        tdb.set_block_and_prefix(block_number, block_id);
        BlockState block_state{tdb, vm};
        // avoid conflict with block reward txn
        Incarnation const incarnation{block_number, Incarnation::LAST_TX - 1u};
        State state{block_state, incarnation};

        for (auto const &[addr, state_delta] : state_overrides.override_sets) {
            // address
            Address address{};
            std::memcpy(address.bytes, addr.data(), sizeof(Address));

            // This would avoid seg-fault on storage override for non-existing
            // accounts
            auto const &account = state.recent_account(address);
            if (MONAD_UNLIKELY(!account.has_value())) {
                state.create_contract(address);
            }

            if (state_delta.balance.has_value()) {
                auto const balance = intx::be::unsafe::load<uint256_t>(
                    state_delta.balance.value().data());
                if (balance >
                    intx::be::load<uint256_t>(
                        state.get_current_balance_pessimistic(address))) {
                    state.add_to_balance(
                        address,
                        balance - intx::be::load<uint256_t>(
                                      state.get_current_balance_pessimistic(
                                          address)));
                }
                else {
                    state.subtract_from_balance(
                        address,
                        intx::be::load<uint256_t>(
                            state.get_current_balance_pessimistic(address)) -
                            balance);
                }
            }

            if (state_delta.nonce.has_value()) {
                state.set_nonce(address, state_delta.nonce.value());
            }

            if (state_delta.code.has_value()) {
                byte_string const code{
                    state_delta.code.value().data(),
                    state_delta.code.value().size()};
                state.set_code(address, code);
            }

            auto const update_state =
                [&](std::map<byte_string, byte_string> const &diff) {
                    for (auto const &[key, value] : diff) {
                        bytes32_t storage_key;
                        bytes32_t storage_value;
                        std::memcpy(
                            storage_key.bytes, key.data(), sizeof(bytes32_t));
                        std::memcpy(
                            storage_value.bytes,
                            value.data(),
                            sizeof(bytes32_t));

                        state.set_storage(address, storage_key, storage_value);
                    }
                };

            // Remove single storage
            if (!state_delta.state_diff.empty()) {
                // we need to access the account first before accessing its
                // storage
                (void)state.get_nonce(address);
                update_state(state_delta.state_diff);
            }

            // Remove all override
            if (!state_delta.state.empty()) {
                state.set_to_state_incarnation(address);
                update_state(state_delta.state);
            }
        }

        // validate_transaction expects nonce to match.
        // However, eth_call doesn't take a nonce parameter.
        // Solving the issue by manually setting nonce to match with the
        // expected nonce
        auto const &acct = state.recent_account(sender);
        enriched_txn.nonce = acct.has_value() ? acct.value().nonce : 0;

        // validate_transaction expects the sender of a transaction is EOA, not
        // CA. However, eth_call allows the sender to be CA to simulate a
        // subroutine. Solving this issue by manually setting account to be EOA
        // for validation
        std::optional<Account> eoa = acct;
        if (eoa.has_value()) {
            eoa.value().code_hash = NULL_HASH;
        }

        // Safe to pass empty code to validation here because the above override
        // will always mark this transaction as coming from an EOA.
        BOOST_OUTCOME_TRY(validate_transaction<traits>(enriched_txn, eoa, {}));

        auto const tx_context = get_tx_context<traits>(
            enriched_txn, sender, header, chain.get_chain_id());

        // TODO: properly initialize revert_transaction?
        EvmcHost<traits> host{call_tracer, tx_context, buffer, state};
        auto execution_result = ExecuteTransactionNoValidation<traits>{
            chain, enriched_txn, sender, authorities, header, 0}(state, host);

        // compute gas_refund and gas_used
        auto const gas_refund = compute_gas_refund<traits>(
            enriched_txn,
            static_cast<uint64_t>(execution_result.gas_left),
            static_cast<uint64_t>(execution_result.gas_refund));
        auto const gas_used = enriched_txn.gas_limit - gas_refund;
        call_tracer.on_finish(gas_used);

        execution_result.gas_refund = static_cast<int64_t>(gas_refund);

        trace::run_tracer(state_tracer, state);

        return execution_result;
    }

    ankerl::unordered_dense::segmented_set<Address>
    combine_senders_and_authorities(
        std::vector<Address> const &senders,
        std::vector<std::vector<std::optional<Address>>> const &authorities)
    {
        ankerl::unordered_dense::segmented_set<Address> senders_and_authorities;

        for (Address const &sender : senders) {
            senders_and_authorities.insert(sender);
        }

        for (auto const &authorities_ : authorities) {
            for (std::optional<Address> const &authority : authorities_) {
                if (authority.has_value()) {
                    senders_and_authorities.insert(authority.value());
                }
            }
        }

        return senders_and_authorities;
    }

    std::pair<
        std::vector<Address>, std::vector<std::vector<std::optional<Address>>>>
    recover_senders_and_authorities(
        std::vector<Transaction> const &transactions,
        monad::fiber::PriorityPool &pool)
    {
        std::vector<Address> senders;
        {
            std::vector<std::optional<Address>> const recovered_senders =
                monad::recover_senders(transactions, pool);
            for (std::optional<Address> const &sender : recovered_senders) {
                MONAD_ASSERT_THROW(sender.has_value(), RECOVER_SENDER_ERR_MSG);
                senders.emplace_back(sender.value());
            }
        }

        std::vector<std::vector<std::optional<Address>>> const authorities =
            monad::recover_authorities(transactions, pool);

        return {std::move(senders), authorities};
    }

    template <Traits traits>
    Result<nlohmann::json> eth_trace_block_or_transaction_impl(
        Chain const &chain, MonadChainContext const &chain_context,
        BlockHeader const &header, std::vector<Transaction> const &transactions,
        bool const trace_transaction, uint64_t const transaction_index,
        BlockState &block_state, LazyBlockHash const &buffer,
        monad::fiber::PriorityPool &pool,
        enum monad_tracer_config tracer_config)
    {
        MONAD_ASSERT(transactions.size() == chain_context.senders.size());
        MONAD_ASSERT(transactions.size() == chain_context.authorities.size());

        auto const revert_transaction = [&chain, &header, &chain_context](
                                            Address const &sender,
                                            Transaction const &tx,
                                            uint64_t const i,
                                            State &state) -> bool {
            if constexpr (is_monad_trait_v<traits>) {
                // If this cast doesn't succeed, then something has gone
                // terribly wrong. It will throw an exception which we let
                // the caller of `eth_trace_block_or_transaction_impl`
                // handle.
                return dynamic_cast<MonadChain const &>(chain)
                    .revert_transaction(
                        header.number,
                        header.timestamp,
                        sender,
                        tx,
                        header.base_fee_per_gas.value_or(0),
                        i,
                        state,
                        chain_context);
            }
            else {
                // Suppress unused parameter warnings
                (void)chain;
                (void)header;
                (void)chain_context;
                (void)sender;
                (void)tx;
                (void)i;
                (void)state;
                return false;
            }
        };

        size_t const transactions_size = [&]() {
            if (trace_transaction) {
                MONAD_ASSERT(
                    transaction_index <
                    static_cast<uint64_t>(transactions.size()));
                return transaction_index + 1;
            }
            return transactions.size();
        }();

        std::span<Transaction const> const transactions_view{
            transactions.data(), transactions_size};
        std::span<Address const> const senders_view{
            chain_context.senders.data(), transactions_size};
        std::span<std::vector<std::optional<Address>> const> const
            authorities_view{
                chain_context.authorities.data(), transactions_size};

        // Execute block header
        execute_block_header<traits>(chain, block_state, header);
        BlockMetrics metrics{};

        // Prepare state tracers and auxiliary noop call tracers.
        std::vector<std::unique_ptr<trace::StateTracer>> state_tracers{};
        state_tracers.reserve(transactions_size);

        // Helper to create a trace log entry of the form:
        //   {"result": { execution trace goes here }, "txHash": "0x..."}
        auto const trace_entry =
            [&transactions](
                uint64_t const transaction_index) -> nlohmann::json {
            bytes32_t const tx_hash = to_bytes(keccak256(
                rlp::encode_transaction(transactions[transaction_index])));
            nlohmann::json entry{
                {"result", nlohmann::json{}},
                {"txHash", std::format("0x{}", evmc::hex(tx_hash))}};
            return entry;
        };

        std::vector<std::unique_ptr<CallTracerBase>> noop_call_tracers{};
        noop_call_tracers.reserve(transactions_size);

        for (size_t i = 0; i < transactions_size; ++i) {
            noop_call_tracers.emplace_back(std::make_unique<NoopCallTracer>());
        }
        std::span<std::unique_ptr<CallTracerBase>> const noop_call_tracers_view{
            noop_call_tracers.data(), transactions_size};

        // Trace single transaction
        if (trace_transaction) {
            // We allocate just one trace entry here as we only need to return
            // the trace result of `transactions[transaction_index]`.

            for (size_t i = 0; i < transactions_size - 1; ++i) {
                state_tracers.emplace_back(
                    std::make_unique<trace::StateTracer>(std::monostate{}));
            }

            nlohmann::json trace = trace_entry(transaction_index);
            state_tracers.emplace_back(
                tracer_config == PRESTATE_TRACER
                    ? std::make_unique<trace::StateTracer>(
                          trace::PrestateTracer{trace["result"]})
                    : std::make_unique<trace::StateTracer>(
                          trace::StateDiffTracer{trace["result"]}));

            std::span<std::unique_ptr<trace::StateTracer>> const
                state_tracers_view{state_tracers.data(), transactions_size};

            BOOST_OUTCOME_TRY(execute_block_transactions<traits>(
                chain,
                header,
                transactions_view,
                senders_view,
                authorities_view,
                block_state,
                buffer,
                pool,
                metrics,
                noop_call_tracers_view,
                state_tracers_view,
                revert_transaction));
            return Result<nlohmann::json>{std::move(trace)};
        }
        else {
            // Trace an entire block
            std::vector<nlohmann::json> traces{};
            traces.reserve(transactions_size);
            for (size_t i = 0; i < transactions_size; ++i) {
                traces.emplace_back(trace_entry(i));
                if (tracer_config == PRESTATE_TRACER) {
                    state_tracers.emplace_back(
                        std::make_unique<trace::StateTracer>(
                            trace::PrestateTracer{traces[i]["result"]}));
                }
                else {
                    state_tracers.emplace_back(
                        std::make_unique<trace::StateTracer>(
                            trace::StateDiffTracer{traces[i]["result"]}));
                }
            }

            std::span<std::unique_ptr<trace::StateTracer>> const
                state_tracers_view{state_tracers.data(), transactions_size};

            BOOST_OUTCOME_TRY(execute_block_transactions<traits>(
                chain,
                header,
                transactions_view,
                senders_view,
                authorities_view,
                block_state,
                buffer,
                pool,
                metrics,
                noop_call_tracers_view,
                state_tracers_view,
                revert_transaction));

            // Compose state traces
            return Result<nlohmann::json>{std::move(traces)};
        }
    }
}

namespace monad
{
    quill::Logger *tracer = nullptr;
}

monad_state_override *monad_state_override_create()
{
    monad_state_override *const m = new monad_state_override();

    return m;
}

void monad_state_override_destroy(monad_state_override *const m)
{
    MONAD_ASSERT(m);
    delete m;
}

void add_override_address(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    byte_string const address{addr, addr + addr_len};

    MONAD_ASSERT(m->override_sets.find(address) == m->override_sets.end());
    m->override_sets.emplace(address, StateOverrideObj{});
}

void set_override_balance(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const balance,
    size_t const balance_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    byte_string const address{addr, addr + addr_len};
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(balance);
    m->override_sets[address].balance = {balance, balance + balance_len};
}

void set_override_nonce(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint64_t const nonce)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    byte_string const address{addr, addr + addr_len};
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    m->override_sets[address].nonce = nonce;
}

void set_override_code(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const code, size_t const code_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    byte_string const address{addr, addr + addr_len};
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(code);
    m->override_sets[address].code = {code, code + code_len};
}

void set_override_state_diff(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const key, size_t const key_len,
    uint8_t const *const value, size_t const value_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    byte_string const address{addr, addr + addr_len};
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(key);
    MONAD_ASSERT(key_len == sizeof(bytes32_t));
    byte_string const k{key, key + key_len};

    MONAD_ASSERT(value);

    auto &state_object = m->override_sets[address].state_diff;
    MONAD_ASSERT(state_object.find(k) == state_object.end());
    state_object.emplace(k, byte_string{value, value + value_len});
}

void set_override_state(
    monad_state_override *const m, uint8_t const *const addr,
    size_t const addr_len, uint8_t const *const key, size_t const key_len,
    uint8_t const *const value, size_t const value_len)
{
    MONAD_ASSERT(m);

    MONAD_ASSERT(addr);
    MONAD_ASSERT(addr_len == sizeof(Address));
    byte_string const address{addr, addr + addr_len};
    MONAD_ASSERT(m->override_sets.find(address) != m->override_sets.end());

    MONAD_ASSERT(key);
    MONAD_ASSERT(key_len == sizeof(bytes32_t));
    byte_string const k{key, key + key_len};

    MONAD_ASSERT(value);

    auto &state_object = m->override_sets[address].state;
    MONAD_ASSERT(state_object.find(k) == state_object.end());
    state_object.emplace(k, byte_string{value, value + value_len});
}

void monad_executor_result_release(monad_executor_result *const result)
{
    MONAD_ASSERT(result);
    if (result->output_data) {
        delete[] result->output_data;
    }

    if (result->message) {
        free(result->message);
    }

    if (result->encoded_trace) {
        delete[] result->encoded_trace;
    }

    delete result;
}

namespace
{
    struct Pool
    {
        enum class Type
        {
            low,
            high
        };

        Pool(Type const type, monad_executor_pool_config const &config)
            : type(type)
            , limit(config.queue_limit)
            , timeout(std::chrono::seconds(config.timeout_sec))
            , pool(config.num_threads, config.num_fibers, true)
        {
        }

        monad_executor_pool_state get_state() const
        {
            return monad_executor_pool_state{
                .num_fibers = pool.num_fibers(),
                .executing_count =
                    executing_count.load(std::memory_order_relaxed),
                .queued_count = queued_count.load(std::memory_order_relaxed),
                .queue_limit = limit,
                .queue_full_count =
                    queue_full_count.load(std::memory_order_relaxed),
            };
        }

        bool try_enqueue()
        {
            auto const current = queued_count.load(std::memory_order_relaxed);
            if (current >= limit) {
                queue_full_count.fetch_add(1, std::memory_order_relaxed);
                return false;
            }
            queued_count.fetch_add(1, std::memory_order_relaxed);
            return true;
        }

        Type type;

        // Maximum number of requests in the queue.
        unsigned limit;

        // Timeout request if it failed to be scheduled in this time.
        std::chrono::seconds timeout;

        // Number of requests currently in the queue.
        std::atomic<unsigned> queued_count{0};

        // Number of requests currently being executed.
        std::atomic<unsigned> executing_count{0};

        // Number of queue full conditions.
        std::atomic<uint64_t> queue_full_count{0};

        // Underlying fiber pool.
        fiber::PriorityPool pool;
    };
}

struct monad_executor
{
    Pool low_gas_pool_;
    Pool high_gas_pool_;
    Pool trace_block_pool_;

    // Sequence number for each call. This is used as a priority of the request,
    // requests started earlier have higher priority.
    std::atomic<uint64_t> call_seq_no_{0};

    mpt::RODb db_;

    // The VM for executing eth calls needs to unconditionally use the
    // interpreter rather than the compiler. If it uses the compiler, then
    // out-of-gas errors can be misreported as generic failures.
    vm::VM vm_{false};

    monad_executor(
        monad_executor_pool_config const &low_pool_config,
        monad_executor_pool_config const &high_pool_config,
        monad_executor_pool_config const &block_pool_config,
        uint64_t const node_lru_max_mem, std::string const &triedb_path)
        : low_gas_pool_{Pool::Type::low, low_pool_config}
        , high_gas_pool_{Pool::Type::high, high_pool_config}
        , trace_block_pool_{Pool::Type::high, block_pool_config}
        , db_{[&] {
            std::vector<std::filesystem::path> paths;
            if (std::filesystem::is_directory(triedb_path)) {
                for (auto const &file :
                     std::filesystem::directory_iterator(triedb_path)) {
                    paths.emplace_back(file.path());
                }
            }
            else {
                paths.emplace_back(triedb_path);
            }

            // create the db instances on the PriorityPool thread so all the
            // thread local storage gets instantiated on the one thread its
            // used
            auto const config = mpt::ReadOnlyOnDiskDbConfig{
                .dbname_paths = paths, .node_lru_max_mem = node_lru_max_mem};
            return mpt::RODb{config};
        }()}
    {
    }

    monad_executor(monad_executor const &) = delete;
    monad_executor &operator=(monad_executor const &) = delete;

    void execute_eth_call(
        monad_chain_config const chain_config, Transaction const &txn,
        BlockHeader const &block_header, Address const &sender,
        uint64_t const block_number, bytes32_t const &block_id,
        monad_state_override const *const overrides,
        void (*complete)(monad_executor_result *, void *user), void *const user,
        monad_tracer_config const tracer_config, bool const gas_specified)
    {
        monad_executor_result *const result = new monad_executor_result();

        Pool *pool =
            gas_specified && txn.gas_limit > MONAD_ETH_CALL_LOW_GAS_LIMIT
                ? &high_gas_pool_
                : &low_gas_pool_;

        submit_eth_call_to_pool(
            chain_config,
            txn,
            block_header,
            sender,
            block_number,
            block_id,
            overrides,
            complete,
            user,
            tracer_config,
            gas_specified,
            std::chrono::steady_clock::now(),
            call_seq_no_.fetch_add(1, std::memory_order_relaxed),
            result,
            *pool);
    }

    void submit_eth_call_to_pool(
        monad_chain_config const chain_config, Transaction const &txn,
        BlockHeader const &block_header, Address const &sender,
        uint64_t const block_number, bytes32_t const &block_id,
        monad_state_override const *const overrides,
        void (*complete)(monad_executor_result *, void *user), void *const user,
        monad_tracer_config const tracer_config, bool const gas_specified,
        std::chrono::steady_clock::time_point const call_begin,
        uint64_t const eth_call_seq_no, monad_executor_result *const result,
        Pool &active_pool)
    {
        if (!active_pool.try_enqueue()) {
            result->status_code = EVMC_REJECTED;
            result->message = strdup(EXCEED_QUEUE_SIZE_ERR_MSG);
            MONAD_ASSERT(result->message);
            complete(result, user);
            return;
        }

        auto const authorities =
            recover_authorities(std::span{&txn, 1}, active_pool.pool);
        MONAD_ASSERT(authorities.size() == 1);

        active_pool.pool.submit(
            eth_call_seq_no,
            [this,
             call_begin = call_begin,
             eth_call_seq_no = eth_call_seq_no,
             chain_config = chain_config,
             orig_txn = txn,
             block_header = block_header,
             block_number = block_number,
             block_id = block_id,
             &db = db_,
             sender = sender,
             authorities = authorities[0],
             result = result,
             complete = complete,
             user = user,
             state_overrides = overrides,
             tracer_config = tracer_config,
             gas_specified = gas_specified,
             active_pool = &active_pool] {
                active_pool->queued_count.fetch_sub(
                    1, std::memory_order_relaxed);
                active_pool->executing_count.fetch_add(
                    1, std::memory_order_relaxed);
                BOOST_SCOPE_EXIT_ALL(&active_pool)
                {
                    active_pool->executing_count.fetch_sub(
                        1, std::memory_order_relaxed);
                };
                try {
                    // check for timeout
                    if (std::chrono::steady_clock::now() - call_begin >
                        active_pool->timeout) {
                        result->status_code = EVMC_REJECTED;
                        result->message = strdup(TIMEOUT_ERR_MSG);
                        MONAD_ASSERT(result->message);
                        complete(result, user);
                        return;
                    }
                    auto transaction = orig_txn;

                    bool const override_with_low_gas_retry_if_oog =
                        active_pool->type == Pool::Type::low &&
                        !gas_specified &&
                        orig_txn.gas_limit > MONAD_ETH_CALL_LOW_GAS_LIMIT;

                    if (override_with_low_gas_retry_if_oog) {
                        // override with low gas limit
                        transaction.gas_limit = MONAD_ETH_CALL_LOW_GAS_LIMIT;
                    }

                    auto const chain =
                        [chain_config] -> std::unique_ptr<Chain> {
                        switch (chain_config) {
                        case CHAIN_CONFIG_ETHEREUM_MAINNET:
                            return std::make_unique<EthereumMainnet>();
                        case CHAIN_CONFIG_MONAD_DEVNET:
                            return std::make_unique<MonadDevnet>();
                        case CHAIN_CONFIG_MONAD_TESTNET:
                            return std::make_unique<MonadTestnet>();
                        case CHAIN_CONFIG_MONAD_MAINNET:
                            return std::make_unique<MonadMainnet>();
                        }
                        MONAD_ASSERT(false);
                    }();

                    LazyBlockHash block_hash_buffer{db, block_number};
                    TrieRODb tdb{db};
                    std::vector<CallFrame> call_frames;
                    nlohmann::json state_trace;
                    std::unique_ptr<CallTracerBase> call_tracer =
                        tracer_config == CALL_TRACER
                            ? std::unique_ptr<CallTracerBase>{std::make_unique<
                                  CallTracer>(transaction, call_frames)}
                            : std::unique_ptr<CallTracerBase>{
                                  std::make_unique<NoopCallTracer>()};
                    auto state_tracer = [&]() -> trace::StateTracer {
                        switch (tracer_config) {
                        case NOOP_TRACER:
                        case CALL_TRACER:
                            return std::monostate{};
                        case PRESTATE_TRACER:
                            return trace::PrestateTracer{state_trace};
                        case STATEDIFF_TRACER:
                            return trace::StateDiffTracer{state_trace};
                        }
                        MONAD_ASSERT(false);
                    }();

                    auto const res = [&]() -> Result<evmc::Result> {
                        if (chain_config == CHAIN_CONFIG_ETHEREUM_MAINNET) {
                            evmc_revision const rev = chain->get_revision(
                                block_header.number, block_header.timestamp);
                            SWITCH_EVM_TRAITS(
                                eth_call_impl,
                                *chain,
                                transaction,
                                block_header,
                                block_number,
                                block_id,
                                sender,
                                authorities,
                                tdb,
                                vm_,
                                block_hash_buffer,
                                *state_overrides,
                                *call_tracer,
                                state_tracer);
                            MONAD_ASSERT(false);
                        }
                        else {
                            auto const rev =
                                dynamic_cast<MonadChain *>(chain.get())
                                    ->get_monad_revision(
                                        block_header.timestamp);
                            SWITCH_MONAD_TRAITS(
                                eth_call_impl,
                                *chain,
                                transaction,
                                block_header,
                                block_number,
                                block_id,
                                sender,
                                authorities,
                                tdb,
                                vm_,
                                block_hash_buffer,
                                *state_overrides,
                                *call_tracer,
                                state_tracer);
                            MONAD_ASSERT(false);
                        }
                    }();

                    if (override_with_low_gas_retry_if_oog &&
                        ((res.has_value() &&
                          (res.value().status_code == EVMC_OUT_OF_GAS ||
                           res.value().status_code == EVMC_REVERT)) ||
                         (res.has_error() &&
                          res.error() == TransactionError::
                                             IntrinsicGasGreaterThanLimit))) {
                        retry_in_high_pool(
                            chain_config,
                            orig_txn,
                            block_header,
                            sender,
                            block_number,
                            block_id,
                            state_overrides,
                            complete,
                            user,
                            tracer_config,
                            call_begin,
                            eth_call_seq_no,
                            result);
                        return;
                    }
                    if (MONAD_UNLIKELY(res.has_error())) {
                        result->status_code = EVMC_REJECTED;
                        result->message = strdup(res.error().message().c_str());
                        MONAD_ASSERT(result->message);
                        complete(result, user);
                        return;
                    }
                    call_complete(
                        transaction,
                        res.assume_value(),
                        result,
                        complete,
                        user,
                        call_frames,
                        state_trace);
                }
                catch (MonadException const &e) {
                    result->status_code = EVMC_INTERNAL_ERROR;
                    result->message = strdup(e.message());
                    MONAD_ASSERT(result->message);
                    complete(result, user);
                }
                catch (...) {
                    result->status_code = EVMC_INTERNAL_ERROR;
                    result->message = strdup(UNEXPECTED_EXCEPTION_ERR_MSG);
                    MONAD_ASSERT(result->message);
                    complete(result, user);
                }
            });
    }

    void call_complete(
        Transaction const &transaction, evmc::Result const &evmc_result,
        monad_executor_result *const result,
        void (*complete)(monad_executor_result *, void *user), void *const user,
        std::vector<CallFrame> const &call_frames,
        nlohmann::json const &state_trace)
    {
        result->status_code = evmc_result.status_code;
        result->gas_used =
            static_cast<int64_t>(transaction.gas_limit) - evmc_result.gas_left;
        result->gas_refund = evmc_result.gas_refund;
        if (evmc_result.output_size > 0) {
            result->output_data = new uint8_t[evmc_result.output_size];
            result->output_data_len = evmc_result.output_size;
            memcpy(
                (uint8_t *)result->output_data,
                evmc_result.output_data,
                evmc_result.output_size);
        }
        else {
            result->output_data = nullptr;
            result->output_data_len = 0;
        }

        if (!call_frames.empty()) {
            byte_string const rlp_call_frames =
                rlp::encode_call_frames(call_frames);
            result->encoded_trace = new uint8_t[rlp_call_frames.size()];
            result->encoded_trace_len = rlp_call_frames.size();
            memcpy(
                (uint8_t *)result->encoded_trace,
                rlp_call_frames.data(),
                rlp_call_frames.size());
        }
        else if (!state_trace.empty()) {
            std::vector<uint8_t> cbor_state_trace =
                nlohmann::json::to_cbor(state_trace);
            result->encoded_trace = new uint8_t[cbor_state_trace.size()];
            result->encoded_trace_len = cbor_state_trace.size();
            memcpy(
                (uint8_t *)result->encoded_trace,
                cbor_state_trace.data(),
                cbor_state_trace.size());
        }
        else {
            result->encoded_trace = nullptr;
            result->encoded_trace_len = 0;
        }
        complete(result, user);
    }

    void retry_in_high_pool(
        monad_chain_config const chain_config, Transaction const &orig_txn,
        BlockHeader const &block_header, Address const &sender,
        uint64_t const block_number, bytes32_t const &block_id,
        monad_state_override const *const overrides,
        void (*complete)(monad_executor_result *, void *user), void *const user,
        monad_tracer_config const tracer_config,
        std::chrono::steady_clock::time_point const call_begin,
        auto const eth_call_seq_no, monad_executor_result *const result)
    {
        // retry in high gas limit pool
        MONAD_ASSERT(orig_txn.gas_limit > MONAD_ETH_CALL_LOW_GAS_LIMIT);

        submit_eth_call_to_pool(
            chain_config,
            orig_txn,
            block_header,
            sender,
            block_number,
            block_id,
            overrides,
            complete,
            user,
            tracer_config,
            false /* gas_specified */,
            call_begin,
            eth_call_seq_no,
            result,
            high_gas_pool_);
    }

    void submit_eth_trace_block_or_transaction_to_pool(
        monad_chain_config const chain_config, BlockHeader const &block_header,
        uint64_t const block_number, bytes32_t const &block_id,
        bytes32_t const &parent_id, bytes32_t const &grandparent_id,
        bool const trace_transaction, uint64_t const transaction_index,
        void (*complete)(monad_executor_result *, void *user), void *const user,
        monad_tracer_config const tracer_config)
    {
        monad_executor_result *const result = new monad_executor_result();

        if (tracer_config != PRESTATE_TRACER &&
            tracer_config != STATEDIFF_TRACER) {
            result->status_code = EVMC_REJECTED;
            result->message = strdup(PRESTATE_TRACER_SUPPORT_ERR_MSG);
            MONAD_ASSERT(result->message);
            complete(result, user);
            return;
        }

        if (block_number == 0) {
            result->status_code = EVMC_REJECTED;
            result->message = strdup(CANNOT_TRACE_GENESIS_ERR_MSG);
            MONAD_ASSERT(result->message);
            complete(result, user);
            return;
        }

        if (!trace_block_pool_.try_enqueue()) {
            result->status_code = EVMC_REJECTED;
            result->message = strdup(EXCEED_QUEUE_SIZE_ERR_MSG);
            MONAD_ASSERT(result->message);
            complete(result, user);
            return;
        }

        auto const priority =
            call_seq_no_.fetch_add(1, std::memory_order_relaxed);
        trace_block_pool_.pool.submit(
            priority,
            [this,
             block_id = block_id,
             block_header = block_header,
             block_number = block_number,
             chain_config = chain_config,
             complete = complete,
             &db = db_,
             fiber_pool = &trace_block_pool_,
             grandparent_id = grandparent_id,
             parent_id = parent_id,
             result = result,
             tracer_config = tracer_config,
             trace_transaction = trace_transaction,
             transaction_index = transaction_index,
             user = user]() {
                fiber_pool->queued_count.fetch_sub(
                    1, std::memory_order_relaxed);
                fiber_pool->executing_count.fetch_add(
                    1, std::memory_order_relaxed);
                try {
                    auto const chain =
                        [chain_config] -> std::unique_ptr<Chain> {
                        switch (chain_config) {
                        case CHAIN_CONFIG_ETHEREUM_MAINNET:
                            return std::make_unique<EthereumMainnet>();
                        case CHAIN_CONFIG_MONAD_DEVNET:
                            return std::make_unique<MonadDevnet>();
                        case CHAIN_CONFIG_MONAD_TESTNET:
                            return std::make_unique<MonadTestnet>();
                        case CHAIN_CONFIG_MONAD_MAINNET:
                            return std::make_unique<MonadMainnet>();
                        }
                        MONAD_ASSERT(false);
                    }();

                    // Load transactions, senders, and authorities for
                    // `block_number`.
                    auto const maybe_transactions =
                        monad::get_transactions(db, block_number, block_id);
                    MONAD_ASSERT_THROW(
                        maybe_transactions.has_value(),
                        TRANSACTIONS_CONTEXT_ERR_MSG);

                    auto const &transactions =
                        maybe_transactions.assume_value();
                    if (trace_transaction) {
                        MONAD_ASSERT_THROW(
                            transaction_index < transactions.size(),
                            TRANSACTION_OUT_OF_BOUNDS_ERR_MSG);
                    }

                    auto const &[senders, authorities] =
                        recover_senders_and_authorities(
                            transactions, fiber_pool->pool);

                    auto const senders_and_authorities =
                        combine_senders_and_authorities(senders, authorities);

                    // Load parent and grandparent senders and authorities
                    std::unique_ptr<
                        ankerl::unordered_dense::segmented_set<Address>>
                        parent_senders_and_authorities = nullptr;
                    std::unique_ptr<
                        ankerl::unordered_dense::segmented_set<Address>>
                        grandparent_senders_and_authorities = nullptr;

                    if (MONAD_LIKELY(block_number > 1)) {
                        auto const parent_transactions =
                            monad::get_transactions(
                                db, block_number - 1, parent_id);
                        MONAD_ASSERT_THROW(
                            parent_transactions.has_value(),
                            PARENT_TRANSACTIONS_CONTEXT_ERR_MSG);
                        auto const &[parent_senders, parent_authorities] =
                            recover_senders_and_authorities(
                                parent_transactions.assume_value(),
                                fiber_pool->pool);
                        parent_senders_and_authorities = std::make_unique<
                            ankerl::unordered_dense::segmented_set<Address>>(
                            combine_senders_and_authorities(
                                parent_senders, parent_authorities));
                    }
                    if (MONAD_LIKELY(block_number > 2)) {
                        auto const grandparent_transactions =
                            monad::get_transactions(
                                db, block_number - 2, grandparent_id);
                        MONAD_ASSERT_THROW(
                            grandparent_transactions.has_value(),
                            GRANDPARENT_TRANSACTIONS_CONTEXT_ERR_MSG);
                        auto const
                            &[grandparent_senders, grandparent_authorities] =
                                recover_senders_and_authorities(
                                    grandparent_transactions.assume_value(),
                                    fiber_pool->pool);
                        grandparent_senders_and_authorities = std::make_unique<
                            ankerl::unordered_dense::segmented_set<Address>>(
                            combine_senders_and_authorities(
                                grandparent_senders, grandparent_authorities));
                    }

                    MonadChainContext const chain_context{
                        .grandparent_senders_and_authorities =
                            grandparent_senders_and_authorities
                                ? grandparent_senders_and_authorities.get()
                                : nullptr,
                        .parent_senders_and_authorities =
                            parent_senders_and_authorities
                                ? parent_senders_and_authorities.get()
                                : nullptr,
                        .senders_and_authorities = senders_and_authorities,
                        .senders = senders,
                        .authorities = authorities};

                    // Set db to parent block state
                    TrieRODb tdb{db};
                    tdb.set_block_and_prefix(block_number - 1, parent_id);
                    BlockState block_state{tdb, vm_};
                    LazyBlockHash block_hash_buffer{db, block_number};

                    auto const res = [&]() -> Result<nlohmann::json> {
                        if (chain_config == CHAIN_CONFIG_ETHEREUM_MAINNET) {
                            evmc_revision const rev = chain->get_revision(
                                block_header.number, block_header.timestamp);
                            SWITCH_EVM_TRAITS(
                                eth_trace_block_or_transaction_impl,
                                *chain,
                                chain_context,
                                block_header,
                                transactions,
                                trace_transaction,
                                transaction_index,
                                block_state,
                                block_hash_buffer,
                                fiber_pool->pool,
                                tracer_config);
                            MONAD_ASSERT(false);
                        }
                        else {
                            auto const rev =
                                dynamic_cast<MonadChain *>(chain.get())
                                    ->get_monad_revision(
                                        block_header.timestamp);
                            SWITCH_MONAD_TRAITS(
                                eth_trace_block_or_transaction_impl,
                                *chain,
                                chain_context,
                                block_header,
                                transactions,
                                trace_transaction,
                                transaction_index,
                                block_state,
                                block_hash_buffer,
                                fiber_pool->pool,
                                tracer_config);
                            MONAD_ASSERT(false);
                        }
                    }();

                    if (MONAD_UNLIKELY(res.has_error())) {
                        result->status_code = EVMC_REJECTED;
                        result->message = strdup(res.error().message().c_str());
                        MONAD_ASSERT(result->message);
                        complete(result, user);
                        return;
                    }

                    nlohmann::json const &trace = res.assume_value();
                    if (trace.empty()) {
                        result->encoded_trace = nullptr;
                        result->encoded_trace_len = 0;
                    }
                    else {
                        std::vector<uint8_t> cbor_state_trace =
                            nlohmann::json::to_cbor(trace);
                        result->encoded_trace =
                            new uint8_t[cbor_state_trace.size()];
                        result->encoded_trace_len = cbor_state_trace.size();
                        memcpy(
                            (uint8_t *)result->encoded_trace,
                            cbor_state_trace.data(),
                            cbor_state_trace.size());
                    }

                    complete(result, user);
                }
                catch (MonadException const &e) {
                    result->status_code = EVMC_INTERNAL_ERROR;
                    result->message = strdup(e.message());
                    MONAD_ASSERT(result->message);
                    complete(result, user);
                }
                catch (...) {
                    result->status_code = EVMC_INTERNAL_ERROR;
                    result->message = strdup(UNEXPECTED_EXCEPTION_ERR_MSG);
                    MONAD_ASSERT(result->message);
                    complete(result, user);
                }
            });
    }
};

monad_executor *monad_executor_create(
    monad_executor_pool_config const low_pool_conf,
    monad_executor_pool_config const high_pool_conf,
    monad_executor_pool_config const block_pool_conf,
    uint64_t const node_lru_max_mem, char const *const dbpath)
{
    MONAD_ASSERT(dbpath);
    std::string const triedb_path{dbpath};

    monad_executor *const e = new monad_executor(
        low_pool_conf,
        high_pool_conf,
        block_pool_conf,
        node_lru_max_mem,
        triedb_path);

    return e;
}

void monad_executor_destroy(monad_executor *const e)
{
    MONAD_ASSERT(e);

    delete e;
}

void monad_executor_eth_call_submit(
    monad_executor *const executor, monad_chain_config const chain_config,
    uint8_t const *const rlp_txn, size_t const rlp_txn_len,
    uint8_t const *const rlp_header, size_t const rlp_header_len,
    uint8_t const *const rlp_sender, size_t const rlp_sender_len,
    uint64_t const block_number, uint8_t const *const rlp_block_id,
    size_t const rlp_block_id_len, monad_state_override const *const overrides,
    void (*complete)(monad_executor_result *result, void *user),
    void *const user, monad_tracer_config const tracer_config,
    bool const gas_specified)
{
    MONAD_ASSERT(executor);

    byte_string_view rlp_tx_view({rlp_txn, rlp_txn_len});
    byte_string_view rlp_header_view({rlp_header, rlp_header_len});
    byte_string_view rlp_sender_view({rlp_sender, rlp_sender_len});
    byte_string_view block_id_view({rlp_block_id, rlp_block_id_len});

    auto const tx_result = rlp::decode_transaction(rlp_tx_view);
    MONAD_ASSERT(!tx_result.has_error());
    MONAD_ASSERT(rlp_tx_view.empty());
    auto const &tx = tx_result.value();

    auto const block_header_result = rlp::decode_block_header(rlp_header_view);
    MONAD_ASSERT(!block_header_result.has_error());
    MONAD_ASSERT(rlp_header_view.empty());
    auto const &block_header = block_header_result.value();

    auto const sender_result = rlp::decode_address(rlp_sender_view);
    MONAD_ASSERT(!sender_result.has_error());
    MONAD_ASSERT(rlp_sender_view.empty());
    auto const sender = sender_result.value();

    auto const block_id_result = rlp::decode_bytes32(block_id_view);
    MONAD_ASSERT(!block_id_result.has_error());
    MONAD_ASSERT(block_id_view.empty());
    auto const block_id = block_id_result.value();

    MONAD_ASSERT(overrides);

    executor->execute_eth_call(
        chain_config,
        tx,
        block_header,
        sender,
        block_number,
        block_id,
        overrides,
        complete,
        user,
        tracer_config,
        gas_specified);
}

struct monad_executor_state monad_executor_get_state(monad_executor *const e)
{
    MONAD_ASSERT(e);
    return monad_executor_state{
        .low_gas_pool_state = e->low_gas_pool_.get_state(),
        .high_gas_pool_state = e->high_gas_pool_.get_state(),
        .trace_block_pool_state = e->trace_block_pool_.get_state(),
    };
}

void monad_executor_run_transactions(
    struct monad_executor *executor, enum monad_chain_config chain_config,
    uint8_t const *rlp_header, size_t rlp_header_len, uint64_t block_number,
    uint8_t const *rlp_block_id, size_t rlp_block_id_len,
    uint8_t const *rlp_parent_block_id, size_t rlp_parent_block_id_len,
    uint8_t const *rlp_grandparent_block_id,
    size_t rlp_grandparent_block_id_len, int64_t const transaction_index,
    void (*complete)(monad_executor_result *, void *user), void *user,
    enum monad_tracer_config tracer_config)
{
    MONAD_ASSERT(executor);

    byte_string_view rlp_header_view({rlp_header, rlp_header_len});
    byte_string_view block_id_view({rlp_block_id, rlp_block_id_len});
    byte_string_view parent_id_view(
        {rlp_parent_block_id, rlp_parent_block_id_len});
    byte_string_view grandparent_id_view(
        {rlp_grandparent_block_id, rlp_grandparent_block_id_len});

    auto const block_header_result = rlp::decode_block_header(rlp_header_view);
    MONAD_ASSERT(!block_header_result.has_error());
    MONAD_ASSERT(rlp_header_view.empty());
    auto const &block_header = block_header_result.value();

    auto const block_id_result = rlp::decode_bytes32(block_id_view);
    MONAD_ASSERT(!block_id_result.has_error());
    MONAD_ASSERT(block_id_view.empty());
    auto const block_id = block_id_result.value();

    auto const parent_id_result = rlp::decode_bytes32(parent_id_view);
    MONAD_ASSERT(!parent_id_result.has_error());
    MONAD_ASSERT(parent_id_view.empty());
    auto const parent_id = parent_id_result.value();

    auto const grandparent_id = [&]() {
        if (grandparent_id_view.size() == 0) {
            return bytes32_t{};
        }
        auto const grandparent_id_result =
            rlp::decode_bytes32(grandparent_id_view);
        MONAD_ASSERT(!grandparent_id_result.has_error());
        MONAD_ASSERT(grandparent_id_view.empty());
        return grandparent_id_result.value();
    }();

    executor->submit_eth_trace_block_or_transaction_to_pool(
        chain_config,
        block_header,
        block_number,
        block_id,
        parent_id,
        grandparent_id,
        transaction_index >= 0,
        static_cast<uint64_t>(transaction_index),
        complete,
        user,
        tracer_config);
}
