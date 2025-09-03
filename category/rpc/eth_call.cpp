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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/lru/lru_cache.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain_config.h>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/evmc_host.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/execute_transaction.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/tx_context.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/monad/chain/monad_testnet2.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/ondisk_db_config.hpp>
#include <category/mpt/util.hpp>
#include <category/rpc/eth_call.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <nlohmann/json.hpp>

#include <quill/Quill.h>

#include <cstring>
#include <filesystem>
#include <memory>
#include <string_view>
#include <variant>
#include <vector>

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
    char const *const UNEXPECTED_EXCEPTION_ERR_MSG = "unexpected error";
    char const *const BLOCKHASH_ERR_MSG =
        "failure to initialize block hash buffer";
    char const *const EXCEED_QUEUE_SIZE_ERR_MSG =
        "failure to submit eth_call to thread pool: queue size exceeded";
    char const *const TIMEOUT_ERR_MSG =
        "failure to execute eth_call: queuing time exceeded timeout threshold";
    using StateOverrideObj = monad_state_override::monad_state_override_object;

    template <Traits traits>
    Result<evmc::Result> eth_call_impl(
        Chain const &chain, Transaction const &txn, BlockHeader const &header,
        uint64_t const block_number, bytes32_t const &block_id,
        Address const &sender,
        std::vector<std::optional<Address>> const &authorities, TrieRODb &tdb,
        vm::VM &vm, BlockHashBufferFinalized const buffer,
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

        size_t const max_code_size =
            chain.get_max_code_size(header.number, header.timestamp);

        BOOST_OUTCOME_TRY(static_validate_transaction<traits>(
            enriched_txn,
            header.base_fee_per_gas,
            header.excess_blob_gas,
            chain.get_chain_id(),
            max_code_size));

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
                    intx::be::load<uint256_t>(state.get_balance(address))) {
                    state.add_to_balance(
                        address,
                        balance - intx::be::load<uint256_t>(
                                      state.get_balance(address)));
                }
                else {
                    state.subtract_from_balance(
                        address,
                        intx::be::load<uint256_t>(state.get_balance(address)) -
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
        EvmcHost<traits> host{
            chain,
            call_tracer,
            tx_context,
            buffer,
            state,
            max_code_size,
            chain.get_max_initcode_size(header.number, header.timestamp)};
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
    byte_string const b{balance, balance + balance_len};
    m->override_sets[address].balance = std::move(b);
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
    byte_string const c{code, code + code_len};
    m->override_sets[address].code = std::move(c);
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
    byte_string const v{value, value + value_len};

    auto &state_object = m->override_sets[address].state_diff;
    MONAD_ASSERT(state_object.find(k) == state_object.end());
    state_object.emplace(k, std::move(v));
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
    byte_string const v{value, value + value_len};

    auto &state_object = m->override_sets[address].state;
    MONAD_ASSERT(state_object.find(k) == state_object.end());
    state_object.emplace(k, std::move(v));
}

void monad_eth_call_result_release(monad_eth_call_result *const result)
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

struct monad_eth_call_executor
{
    using BlockHashCache = LruCache<uint64_t, bytes32_t>;

    fiber::PriorityPool low_gas_pool_;
    fiber::PriorityPool high_gas_pool_;

    unsigned high_pool_queue_limit_{20};
    std::chrono::seconds low_pool_timeout_{2};
    std::chrono::seconds high_pool_timeout_{30};

    // counters
    uint64_t call_count_{0};
    std::atomic<unsigned> high_pool_queued_count_{0};

    mpt::RODb db_;

    // The VM for executing eth calls needs to unconditionally use the
    // interpreter rather than the compiler. If it uses the compiler, then
    // out-of-gas errors can be misreported as generic failures.
    vm::VM vm_{false};

    BlockHashCache blockhash_cache_{7200};

    monad_eth_call_executor(
        unsigned const num_threads, unsigned const num_fibers,
        uint64_t const node_lru_max_mem, unsigned const low_pool_timeout_sec,
        unsigned const high_pool_timeout_sec, std::string const &triedb_path)
        : low_gas_pool_{num_threads, num_fibers, true}
        , high_gas_pool_{1, 2, true}
        , low_pool_timeout_{low_pool_timeout_sec}
        , high_pool_timeout_{high_pool_timeout_sec}
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

    monad_eth_call_executor(monad_eth_call_executor const &) = delete;
    monad_eth_call_executor &
    operator=(monad_eth_call_executor const &) = delete;

    std::unique_ptr<BlockHashBufferFinalized>
    create_blockhash_buffer(uint64_t const block_number)
    {
        std::unique_ptr<BlockHashBufferFinalized> buffer{
            new BlockHashBufferFinalized{}};

        auto const get_block_hash_from_db =
            [&db = db_](uint64_t const b) -> Result<bytes32_t> {
            BOOST_OUTCOME_TRY(
                auto header_cursor,
                db.find(
                    mpt::concat(
                        FINALIZED_NIBBLE,
                        mpt::NibblesView{block_header_nibbles}),
                    b));
            return to_bytes(keccak256(header_cursor.node->value()));
        };
        for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
             b < block_number;
             ++b) {
            {
                BlockHashCache::ConstAccessor acc;
                if (blockhash_cache_.find(acc, b)) {
                    buffer->set(b, acc->second.value_);
                    continue;
                }
            }
            auto const h = get_block_hash_from_db(b);
            if (h.has_value()) {
                buffer->set(b, h.value());
                blockhash_cache_.insert(b, h.value());
            }
            else {
                LOG_WARNING(
                    "Could not query block header {} from TrieRODb -- "
                    "{}",
                    b,
                    h.assume_error().message().c_str());
                return nullptr;
            }
        }
        return buffer;
    }

    void execute_eth_call(
        monad_chain_config const chain_config, Transaction const &txn,
        BlockHeader const &block_header, Address const &sender,
        uint64_t const block_number, bytes32_t const &block_id,
        monad_state_override const *const overrides,
        void (*complete)(monad_eth_call_result *, void *user), void *const user,
        monad_tracer_config const tracer_config, bool const gas_specified)
    {
        monad_eth_call_result *const result = new monad_eth_call_result();

        bool const use_high_gas_pool =
            (gas_specified && txn.gas_limit > MONAD_ETH_CALL_LOW_GAS_LIMIT);

        if (use_high_gas_pool) {
            if (high_pool_queued_count_.load(std::memory_order_acquire) >=
                high_pool_queue_limit_) {
                result->status_code = EVMC_REJECTED;
                result->message = strdup(EXCEED_QUEUE_SIZE_ERR_MSG);
                MONAD_ASSERT(result->message);
                complete(result, user);
                return;
            }
            ++high_pool_queued_count_;
        }
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
            call_count_++,
            result,
            use_high_gas_pool);
    }

    void submit_eth_call_to_pool(
        monad_chain_config const chain_config, Transaction const &txn,
        BlockHeader const &block_header, Address const &sender,
        uint64_t const block_number, bytes32_t const &block_id,
        monad_state_override const *const overrides,
        void (*complete)(monad_eth_call_result *, void *user), void *const user,
        monad_tracer_config const tracer_config, bool const gas_specified,
        std::chrono::steady_clock::time_point const call_begin,
        uint64_t const eth_call_seq_no, monad_eth_call_result *const result,
        bool const use_high_gas_pool)
    {
        auto &active_pool = use_high_gas_pool ? high_gas_pool_ : low_gas_pool_;

        auto const authorities = recover_authorities({txn}, active_pool);
        MONAD_ASSERT(authorities.size() == 1);

        active_pool.submit(
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
             use_high_gas_pool = use_high_gas_pool,
             timeout =
                 use_high_gas_pool ? high_pool_timeout_ : low_pool_timeout_] {
                try {
                    if (use_high_gas_pool) {
                        --high_pool_queued_count_;
                    }
                    // check for timeout
                    if (std::chrono::steady_clock::now() - call_begin >
                        timeout) {
                        result->status_code = EVMC_REJECTED;
                        result->message = strdup(TIMEOUT_ERR_MSG);
                        MONAD_ASSERT(result->message);
                        complete(result, user);
                        return;
                    }

                    auto transaction = orig_txn;

                    bool const override_with_low_gas_retry_if_oog =
                        !use_high_gas_pool && !gas_specified &&
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
                        case CHAIN_CONFIG_MONAD_TESTNET2:
                            return std::make_unique<MonadTestnet2>();
                        }
                        MONAD_ASSERT(false);
                    }();

                    auto const block_hash_buffer =
                        create_blockhash_buffer(block_number);
                    if (block_hash_buffer == nullptr) {
                        result->status_code = EVMC_REJECTED;
                        result->message = strdup(BLOCKHASH_ERR_MSG);
                        MONAD_ASSERT(result->message);
                        complete(result, user);
                        return;
                    }

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
                                *block_hash_buffer,
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
                                *block_hash_buffer,
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
        monad_eth_call_result *const result,
        void (*complete)(monad_eth_call_result *, void *user), void *const user,
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
        void (*complete)(monad_eth_call_result *, void *user), void *const user,
        monad_tracer_config const tracer_config,
        std::chrono::steady_clock::time_point const call_begin,
        auto const eth_call_seq_no, monad_eth_call_result *const result)
    {
        // retry in high gas limit pool
        MONAD_ASSERT(orig_txn.gas_limit > MONAD_ETH_CALL_LOW_GAS_LIMIT);

        if (high_pool_queued_count_.load(std::memory_order_acquire) >=
            high_pool_queue_limit_) {
            result->status_code = EVMC_REJECTED;
            result->message = strdup(EXCEED_QUEUE_SIZE_ERR_MSG);
            MONAD_ASSERT(result->message);
            complete(result, user);
            return;
        }

        ++high_pool_queued_count_;
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
            true /* use_high_gas_pool */);
    }
};

monad_eth_call_executor *monad_eth_call_executor_create(
    unsigned const num_threads, unsigned const num_fibers,
    uint64_t const node_lru_max_mem, unsigned const low_pool_timeout_sec,
    unsigned const high_pool_timeout_sec, char const *const dbpath)
{
    MONAD_ASSERT(dbpath);
    std::string const triedb_path{dbpath};

    monad_eth_call_executor *const e = new monad_eth_call_executor(
        num_threads,
        num_fibers,
        node_lru_max_mem,
        low_pool_timeout_sec,
        high_pool_timeout_sec,
        triedb_path);

    return e;
}

void monad_eth_call_executor_destroy(monad_eth_call_executor *const e)
{
    MONAD_ASSERT(e);

    delete e;
}

void monad_eth_call_executor_submit(
    monad_eth_call_executor *const executor,
    monad_chain_config const chain_config, uint8_t const *const rlp_txn,
    size_t const rlp_txn_len, uint8_t const *const rlp_header,
    size_t const rlp_header_len, uint8_t const *const rlp_sender,
    size_t const rlp_sender_len, uint64_t const block_number,
    uint8_t const *const rlp_block_id, size_t const rlp_block_id_len,
    monad_state_override const *const overrides,
    void (*complete)(monad_eth_call_result *result, void *user),
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
    auto const tx = tx_result.value();

    auto const block_header_result = rlp::decode_block_header(rlp_header_view);
    MONAD_ASSERT(!block_header_result.has_error());
    MONAD_ASSERT(rlp_header_view.empty());
    auto const block_header = block_header_result.value();

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
