#include <monad/chain/chain_config.h>
#include <monad/chain/ethereum_mainnet.hpp>
#include <monad/chain/monad_devnet.hpp>
#include <monad/chain/monad_testnet.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/rlp/address_rlp.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/rlp/transaction_rlp.hpp>
#include <monad/core/transaction.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/execution/evmc_host.hpp>
#include <monad/execution/execute_transaction.hpp>
#include <monad/execution/switch_evmc_revision.hpp>
#include <monad/execution/tx_context.hpp>
#include <monad/execution/validate_transaction.hpp>
#include <monad/fiber/priority_pool.hpp>
#include <monad/lru/static_lru_cache.hpp>
#include <monad/mpt/util.hpp>
#include <monad/rpc/eth_call.h>
#include <monad/state2/block_state.hpp>
#include <monad/state3/state.hpp>
#include <monad/types/incarnation.hpp>

#include <boost/fiber/future/promise.hpp>
#include <boost/outcome/try.hpp>

#include <quill/Quill.h>

#include <cstring>
#include <filesystem>
#include <string_view>
#include <variant>
#include <vector>

using namespace monad;

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
    char const *const BLOCKHASH_ERR_MSG =
        "failure to initialize block hash buffer";

    using StateOverrideObj = monad_state_override::monad_state_override_object;

    template <evmc_revision rev>
    Result<evmc::Result> eth_call_impl(
        Chain const &chain, Transaction const &txn, BlockHeader const &header,
        uint64_t const block_number, uint64_t const round,
        Address const &sender, TrieDb &tdb,
        std::shared_ptr<BlockHashBufferFinalized const> const buffer,
        monad_state_override const &state_overrides)
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

        BOOST_OUTCOME_TRY(static_validate_transaction<rev>(
            enriched_txn,
            header.base_fee_per_gas,
            chain.get_chain_id(),
            max_code_size));

        tdb.set_block_and_round(
            block_number,
            round == mpt::INVALID_ROUND_NUM ? std::nullopt
                                            : std::make_optional(round));
        BlockState block_state{tdb};
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

        BOOST_OUTCOME_TRY(validate_transaction(enriched_txn, eoa));

        auto const tx_context = get_tx_context<rev>(
            enriched_txn, sender, header, chain.get_chain_id());
        NoopCallTracer call_tracer;
        EvmcHost<rev> host{
            call_tracer, tx_context, *buffer, state, max_code_size};
        auto result = execute_impl_no_validation<rev>(
            state,
            host,
            enriched_txn,
            sender,
            header.base_fee_per_gas.value_or(0),
            header.beneficiary,
            max_code_size);
        return std::move(result.evmc_result);
    }

    Result<evmc::Result> eth_call_impl(
        Chain const &chain, evmc_revision const rev, Transaction const &txn,
        BlockHeader const &header, uint64_t const block_number,
        uint64_t const round, Address const &sender, TrieDb &tdb,
        std::shared_ptr<BlockHashBufferFinalized const> const buffer,
        monad_state_override const &state_overrides)
    {
        SWITCH_EVMC_REVISION(
            eth_call_impl,
            chain,
            txn,
            header,
            block_number,
            round,
            sender,
            tdb,
            buffer,
            state_overrides);
        MONAD_ASSERT(false);
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

    delete result;
}

struct monad_eth_call_executor
{
    using BlockHashCache = static_lru_cache<uint64_t, bytes32_t>;

    using DbGetPromise =
        boost::fibers::promise<std::variant<byte_string, std::string>>;

    fiber::PriorityPool pool_;

    std::shared_ptr<mpt::AsyncIOContext> async_io_{};
    std::shared_ptr<mpt::Db> latest_db_{};
    std::shared_ptr<mpt::Db> db_{};
    std::shared_ptr<TrieDb> latest_tdb_{};
    std::shared_ptr<TrieDb> tdb_{};

    uint64_t last_latest_version_{0};

    BlockHashCache blockhash_cache_{7200};
    std::shared_ptr<BlockHashBufferFinalized> last_buffer_{};
    std::optional<uint64_t> last_block_number_{};

    monad_eth_call_executor(
        unsigned const num_fibers, std::string const &triedb_path)
        : pool_{1, num_fibers}
    {
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

        // create the db instances on the PriorityPool thread so all the thread
        // local storage gets instantiated on the one thread its used
        auto promise = std::make_shared<boost::fibers::promise<void>>();
        pool_.submit(
            0,
            [&paths = paths,
             &async_io = async_io_,
             &db = db_,
             &latest_db = latest_db_,
             &tdb = tdb_,
             &latest_tdb = latest_tdb_,
             promise = promise] {
                async_io.reset(new mpt::AsyncIOContext{
                    mpt::ReadOnlyOnDiskDbConfig{.dbname_paths = paths}});
                db.reset(new mpt::Db{*async_io});
                latest_db.reset(new mpt::Db{*async_io});
                tdb.reset(new TrieDb{*db});
                latest_tdb.reset(new TrieDb{*latest_db});
                promise->set_value();
            });
        promise->get_future().get();
        return;
    }

    monad_eth_call_executor(monad_eth_call_executor const &) = delete;
    monad_eth_call_executor &
    operator=(monad_eth_call_executor const &) = delete;

    // destroy the db instances on the same thread they were created,
    // the PriorityPool thread
    ~monad_eth_call_executor()
    {
        auto promise = std::make_shared<boost::fibers::promise<void>>();
        pool_.submit(
            0,
            [&async_io = async_io_,
             &db = db_,
             &latest_db = latest_db_,
             &tdb = tdb_,
             &latest_tdb = latest_tdb_,
             promise = promise] {
                latest_tdb.reset();
                latest_db.reset();
                tdb.reset();
                db.reset();
                async_io.reset();
                promise->set_value();
            });
        promise->get_future().get();
    }

    std::shared_ptr<BlockHashBufferFinalized const>
    create_blockhash_buffer(uint64_t const block_number)
    {
        if (!last_block_number_ || *last_block_number_ != block_number) {
            last_buffer_.reset(new BlockHashBufferFinalized{});
            BlockHashCache::ConstAccessor acc;
            for (uint64_t b = block_number < 256 ? 0 : block_number - 256;
                 b < block_number;
                 ++b) {
                if (blockhash_cache_.find(acc, b)) {
                    last_buffer_->set(b, acc->second->val);
                    continue;
                }

                auto const promise = std::make_shared<DbGetPromise>();
                pool_.submit(0, [db = db_, b = b, promise = promise] {
                    auto const h = db->get(
                        mpt::concat(
                            FINALIZED_NIBBLE,
                            mpt::NibblesView{block_header_nibbles}),
                        b);
                    if (h.has_value()) {
                        promise->set_value(byte_string{h.value()});
                    }
                    else {
                        promise->set_value(
                            std::string{h.error().message().c_str()});
                    }
                });
                auto const header_result = promise->get_future().get();

                if (auto const header = std::get_if<0>(&header_result)) {
                    auto const h = to_bytes(keccak256(*header));
                    last_buffer_->set(b, h);
                    blockhash_cache_.insert(b, h);
                }
                else {
                    auto const err = std::get<1>(header_result);
                    LOG_WARNING(
                        "Could not query block header {} from TrieDb -- {}",
                        b,
                        err.c_str());
                    return nullptr;
                }
            }
            last_block_number_ = block_number;
        }
        return last_buffer_;
    }

    void execute_eth_call(
        monad_chain_config const chain_config, Transaction const &txn,
        BlockHeader const &block_header, Address const &sender,
        uint64_t const block_number, uint64_t const block_round,
        monad_state_override const *const overrides,
        void (*complete)(monad_eth_call_result *, void *user), void *const user)
    {
        if (block_number > last_latest_version_) {
            last_latest_version_ = block_number;
        }

        monad_eth_call_result *const result = new monad_eth_call_result();

        auto const blk_hash_buffer = create_blockhash_buffer(block_number);
        if (blk_hash_buffer == nullptr) {
            result->status_code = EVMC_REJECTED;
            result->message = strdup(BLOCKHASH_ERR_MSG);
            MONAD_ASSERT(result->message);
            complete(result, user);
            return;
        }

        pool_.submit(
            0,
            [chain_config = chain_config,
             transaction = txn,
             block_header = block_header,
             block_number = block_number,
             block_round = block_round,
             sender = sender,
             tdb = block_number == last_latest_version_ ? latest_tdb_ : tdb_,
             block_hash_buffer = blk_hash_buffer,
             result = result,
             complete = complete,
             user = user,
             state_overrides = overrides] {
                auto const chain = [chain_config] -> std::unique_ptr<Chain> {
                    switch (chain_config) {
                    case CHAIN_CONFIG_ETHEREUM_MAINNET:
                        return std::make_unique<EthereumMainnet>();
                    case CHAIN_CONFIG_MONAD_DEVNET:
                        return std::make_unique<MonadDevnet>();
                    case CHAIN_CONFIG_MONAD_TESTNET:
                        return std::make_unique<MonadTestnet>();
                    }
                    MONAD_ASSERT(false);
                }();

                evmc_revision const rev = chain->get_revision(
                    block_header.number, block_header.timestamp);

                auto const res = eth_call_impl(
                    *chain,
                    rev,
                    transaction,
                    block_header,
                    block_number,
                    block_round,
                    sender,
                    *tdb,
                    block_hash_buffer,
                    *state_overrides);

                if (MONAD_UNLIKELY(res.has_error())) {
                    result->status_code = EVMC_REJECTED;
                    result->message = strdup(res.error().message().c_str());
                    MONAD_ASSERT(result->message);
                    complete(result, user);
                    return;
                }

                auto const &res_value = res.assume_value();

                result->status_code = res_value.status_code;
                result->gas_used = static_cast<int64_t>(transaction.gas_limit) -
                                   res_value.gas_left;
                result->gas_refund = res_value.gas_refund;
                if (res_value.output_size > 0) {
                    result->output_data = new uint8_t[res_value.output_size];
                    result->output_data_len = res_value.output_size;
                    memcpy(
                        (uint8_t *)result->output_data,
                        res_value.output_data,
                        res_value.output_size);
                }
                else {
                    result->output_data = nullptr;
                    result->output_data_len = 0;
                }

                complete(result, user);
            });
    }
};

monad_eth_call_executor *monad_eth_call_executor_create(
    unsigned const num_fibers, char const *const dbpath)
{
    MONAD_ASSERT(dbpath);
    std::string const triedb_path{dbpath};

    monad_eth_call_executor *const e =
        new monad_eth_call_executor(num_fibers, triedb_path);

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
    uint64_t const block_round, monad_state_override const *const overrides,
    void (*complete)(monad_eth_call_result *result, void *user),
    void *const user)
{
    MONAD_ASSERT(executor);

    byte_string_view rlp_tx_view({rlp_txn, rlp_txn_len});
    byte_string_view rlp_header_view({rlp_header, rlp_header_len});
    byte_string_view rlp_sender_view({rlp_sender, rlp_sender_len});

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

    MONAD_ASSERT(overrides);

    executor->execute_eth_call(
        chain_config,
        tx,
        block_header,
        sender,
        block_number,
        block_round,
        overrides,
        complete,
        user);
}
