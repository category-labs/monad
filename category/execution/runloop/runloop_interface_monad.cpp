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

#include <category/core/fiber/priority_pool.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/runloop/runloop_interface_monad.h>
#include <category/execution/runloop/runloop_monad.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <filesystem>
#include <memory>

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/handlers/FileHandler.h>

using namespace monad;
namespace fs = std::filesystem;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

unsigned const sq_thread_cpu = 7;
quill::LogLevel const log_level = quill::LogLevel::Info;
unsigned const nthreads = 4;
unsigned const nfibers = 256;

unsigned const mainnet_chain_id = 143;
unsigned const devnet_chain_id = 20143;
unsigned const testnet_chain_id = 10143;

std::unique_ptr<MonadChain>
monad_chain_from_chain_id(uint64_t chain_id)
{
    if (chain_id == mainnet_chain_id) {
        return std::make_unique<MonadMainnet>();
    }
    if (chain_id == devnet_chain_id) {
        return std::make_unique<MonadDevnet>();
    }
    if (chain_id == testnet_chain_id) {
        return std::make_unique<MonadTestnet>();
    }
    MONAD_ABORT("invalid chain id");
}

struct AccountOverride
{
    uint256_t balance;
};

struct MonadRunloopDbCache: public Db
{
    std::unordered_map<Address, AccountOverride> account_override;
    DbCache &db_cache;

    MonadRunloopDbCache(DbCache &dbc)
        : db_cache{dbc}
    {
    }

    virtual std::optional<Account>
    read_account(Address const &address) override
    {
        auto acct = db_cache.read_account(address);
        auto const over_it = account_override.find(address);
        if (over_it == account_override.end()) {
            return acct;
        }
        Account ret;
        if (acct.has_value()) {
            ret = *acct;
        }
        auto const &over = over_it->second;
        ret.balance = over.balance;
        return ret;
    }

    virtual bytes32_t read_storage(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &key) override
    {
        return db_cache.read_storage(address, incarnation, key);
    }

    virtual vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        return db_cache.read_code(code_hash);
    }

    virtual void set_block_and_prefix(
        uint64_t const block_number,
        bytes32_t const &block_id = bytes32_t{}) override
    {
        db_cache.set_block_and_prefix(block_number, block_id);
    }

    virtual void
    finalize(uint64_t const block_number, bytes32_t const &block_id) override
    {
        db_cache.finalize(block_number, block_id);
    }

    virtual void update_verified_block(uint64_t const block_number) override
    {
        db_cache.update_verified_block(block_number);
    }

    virtual void update_voted_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        db_cache.update_voted_metadata(block_number, block_id);
    }

    virtual void update_proposed_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        db_cache.update_proposed_metadata(block_number, block_id);
    }

    virtual void commit(
        StateDeltas const &, Code const &, bytes32_t const &,
        BlockHeader const &, std::vector<Receipt> const &,
        std::vector<std::vector<CallFrame>> const &,
        std::vector<Address> const &, std::vector<Transaction> const &,
        std::vector<BlockHeader> const &,
        std::optional<std::vector<Withdrawal>> const &) override
    {
        MONAD_ABORT("Use commit function with unique_ptr arg.");
    }

    virtual void commit(
        std::unique_ptr<StateDeltas> pre_state_deltas, Code const &code,
        bytes32_t const &block_id, BlockHeader const &header,
        std::vector<Receipt> const &receipts = {},
        std::vector<std::vector<CallFrame>> const &call_frames = {},
        std::vector<Address> const &senders = {},
        std::vector<Transaction> const &transactions = {},
        std::vector<BlockHeader> const &ommers = {},
        std::optional<std::vector<Withdrawal>> const &withdrawals = {}) override
    {
        auto state_deltas = std::make_unique<StateDeltas>();
        for (auto const &[a, sd] : *pre_state_deltas) {
            auto over_it = account_override.find(a);
            if (over_it == account_override.end()) {
                state_deltas->emplace(a, sd);
            }
            else {
                auto const orig = read_account(a);
                AccountDelta const ad{orig, sd.account.second};
                StateDelta new_sd{ad, sd.storage};
                state_deltas->emplace(a, new_sd);
                account_override.erase(over_it);
            }
        }
        for (auto const &[a, over] : account_override) {
            auto const orig_acct = read_account(a);
            if (orig_acct) {
                auto over_acct = orig_acct;
                over_acct->balance = over.balance;
                AccountDelta const ad{orig_acct, over_acct};
                StateDelta const sd{ad, {}};
                state_deltas->emplace(a, sd);
            }
            else {
                auto over_acct = std::make_optional<Account>();
                over_acct->balance = over.balance;
                AccountDelta const ad{std::nullopt, over_acct};
                StateDelta const sd{ad, {}};
                state_deltas->emplace(a, sd);
            }
        }
        MONAD_ASSERT(account_override.empty());
        db_cache.commit(
            std::move(state_deltas),
            code,
            block_id,
            header,
            receipts,
            call_frames,
            senders,
            transactions,
            ommers,
            withdrawals);
    }

    virtual BlockHeader read_eth_header() override
    {
        return db_cache.read_eth_header();
    }

    virtual bytes32_t state_root() override
    {
        return db_cache.state_root();
    }

    virtual bytes32_t receipts_root() override
    {
        return db_cache.receipts_root();
    }

    virtual bytes32_t transactions_root() override
    {
        return db_cache.transactions_root();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        return db_cache.withdrawals_root();
    }

    virtual std::string print_stats() override
    {
        return db_cache.print_stats();
    }

    virtual uint64_t get_block_number() const override
    {
        return db_cache.get_block_number();
    }
};

struct MonadRunloopImpl
{
    std::unique_ptr<MonadChain> chain;
    fs::path ledger_dir;
    OnDiskMachine db_machine;
    mpt::Db raw_db;
    TrieDb triedb;
    DbCache db_cache;
    MonadRunloopDbCache db;
    vm::VM vm;
    BlockHashBufferFinalized block_hash_buffer;
    fiber::PriorityPool priority_pool;
    uint64_t finalized_block_num;

    MonadRunloopImpl(
        uint64_t chain_id,
        char const *ledger_path,
        char const *db_path);
};

MonadRunloopImpl::MonadRunloopImpl(
    uint64_t chain_id,
    char const *ledger_path,
    char const *db_path)
    : chain{monad_chain_from_chain_id(chain_id)}
    , ledger_dir{ledger_path}
    , db_machine{}
    , raw_db{
        db_machine,
        mpt::OnDiskDbConfig{
            .append = true,
            .compaction = true,
            .rewind_to_latest_finalized = true,
            .rd_buffers = 8192,
            .wr_buffers = 32,
            .uring_entries = 128,
            .sq_thread_cpu = sq_thread_cpu,
            .dbname_paths = {fs::path{db_path}}}}
    , triedb{raw_db}
    , db_cache{triedb}
    , db{db_cache}
    , vm{}
    , block_hash_buffer{}
    , priority_pool{nthreads, nfibers}
    , finalized_block_num{}
{
    if (triedb.get_root() == nullptr) {
        LOG_INFO("loading from genesis");
        GenesisState const genesis_state = chain->get_genesis_state();
        load_genesis_state(genesis_state, triedb);
    }
    else {
        LOG_INFO("loading from previous DB state");
    }

    uint64_t const init_block_num = triedb.get_block_number();
    uint64_t const start_block_num = init_block_num + 1;

    LOG_INFO("Init block number = {}", init_block_num);

    mpt::AsyncIOContext io_ctx{mpt::ReadOnlyOnDiskDbConfig{
        .sq_thread_cpu = sq_thread_cpu, .dbname_paths = {fs::path{db_path}}}};
    mpt::Db rodb{io_ctx};
    bool const have_headers = init_block_hash_buffer_from_triedb(
        rodb,
        start_block_num,
        block_hash_buffer);
    if (!have_headers) {
        BlockDb block_db{ledger_path};
        MONAD_ASSERT(chain_id == mainnet_chain_id);
        MONAD_ASSERT(init_block_hash_buffer_from_blockdb(
            block_db, start_block_num, block_hash_buffer));
    }
}

MonadRunloopImpl *to_impl(MonadRunloop *x)
{
    return reinterpret_cast<MonadRunloopImpl *>(x);
}

MonadRunloop *from_impl(MonadRunloopImpl *x)
{
    return reinterpret_cast<MonadRunloop *>(x);
}

Address to_address(MonadRunloopAddress const *a)
{
    return std::bit_cast<Address>(*a);
}

uint256_t to_uint256(MonadRunloopWord const *x)
{
    return intx::be::load<uint256_t>(*x);
}

MONAD_ANONYMOUS_NAMESPACE_END

extern "C" MonadRunloop *monad_runloop_new(
    uint64_t chain_id, char const *ledger_path, char const *db_path)
{
    auto stdout_handler = quill::stdout_handler();
    stdout_handler->set_pattern(
        "%(time) [%(thread_id)] %(file_name):%(line_number) LOG_%(log_level)\t"
        "%(message)",
        "%Y-%m-%d %H:%M:%S.%Qns",
        quill::Timezone::GmtTime);
    quill::Config quill_cfg;
    quill_cfg.default_handlers.emplace_back(stdout_handler);
    quill::configure(quill_cfg);
    quill::start(true);

    quill::get_root_logger()->set_log_level(log_level);
    return from_impl(new MonadRunloopImpl{chain_id, ledger_path, db_path});
}

extern "C" void monad_runloop_delete(MonadRunloop *runloop)
{
    delete to_impl(runloop);
}

extern "C" void monad_runloop_run(MonadRunloop *pre_runloop, uint64_t nblocks)
try {
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);

    auto const block_num_before = runloop->finalized_block_num;

    sig_atomic_t const stop = 0;
    auto const result = runloop_monad(
        *runloop->chain,
        runloop->ledger_dir,
        runloop->raw_db,
        runloop->db,
        runloop->vm,
        runloop->block_hash_buffer,
        runloop->priority_pool,
        runloop->finalized_block_num,
        runloop->finalized_block_num + nblocks,
        stop,
        /* enable_tracing = */ false);

    auto const block_num_after = runloop->finalized_block_num;

    if (MONAD_UNLIKELY(result.has_error())) {
        LOG_ERROR(
            "block {} failed with: {}",
            block_num_after,
            result.assume_error().message().c_str());
        MONAD_ABORT();
    }
    MONAD_ASSERT(block_num_after - block_num_before == nblocks);
}
catch (MonadException const &e) {
    e.print();
    std::terminate();
}

extern "C" void monad_runloop_set_balance(
    MonadRunloop *pre_runloop,
    MonadRunloopAddress const *raw_addr,
    MonadRunloopWord const *raw_bal)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    auto const addr = to_address(raw_addr);
    auto const bal = to_uint256(raw_bal);
    runloop->db.account_override[addr].balance = bal;
}

extern "C" void monad_runloop_get_balance(
    MonadRunloop *pre_runloop,
    MonadRunloopAddress const *raw_addr,
    MonadRunloopWord *result_balance)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    auto const addr = to_address(raw_addr);
    auto const acct = runloop->db.read_account(addr);
    uint256_t bal;
    if (acct) {
        bal = acct->balance;
    }
    intx::be::store(result_balance->bytes, bal);
}

extern "C" void monad_runloop_get_state_root(
    MonadRunloop *pre_runloop,
    MonadRunloopWord *result_state_root)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    *result_state_root =
        std::bit_cast<MonadRunloopWord>(runloop->db.state_root());
}
