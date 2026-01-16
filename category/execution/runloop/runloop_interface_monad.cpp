// Copyright (C) 2025-26 Category Labs, Inc.
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
#include <category/core/log.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_buffer/util.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/chain/monad_mainnet.hpp>
#include <category/execution/monad/chain/monad_testnet.hpp>
#include <category/execution/runloop/runloop_interface_monad.h>
#include <category/execution/runloop/runloop_monad.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <filesystem>
#include <memory>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

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

std::unique_ptr<MonadChain> monad_chain_from_chain_id(uint64_t const chain_id)
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

using AccountOverrideMap = std::unordered_map<Address, AccountOverride>;

class MonadRunloopTrieDb : public Db
{
    Db &triedb_;
    AccountOverrideMap const &account_override_;

public:
    MonadRunloopTrieDb(Db &db, AccountOverrideMap const &account_override)
        : triedb_{db}
        , account_override_{account_override}
    {
    }

    std::optional<Account> read_underlying_account(Address const &address)
    {
        return triedb_.read_account(address);
    }

    virtual bool is_page_encoded() const override
    {
        return triedb_.is_page_encoded();
    }

    virtual std::optional<Account> read_account(Address const &address) override
    {
        auto acct = triedb_.read_account(address);
        auto const over_it = account_override_.find(address);
        if (over_it == account_override_.end()) {
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
        return triedb_.read_storage(address, incarnation, key);
    }

    virtual storage_page_t read_storage_page(
        Address const &address, Incarnation const incarnation,
        bytes32_t const &page_key) override
    {
        return triedb_.read_storage_page(address, incarnation, page_key);
    }

    virtual vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        return triedb_.read_code(code_hash);
    }

    virtual void set_block_and_prefix(
        uint64_t const block_number,
        bytes32_t const &block_id = bytes32_t{}) override
    {
        triedb_.set_block_and_prefix(block_number, block_id);
    }

    virtual void
    finalize(uint64_t const block_number, bytes32_t const &block_id) override
    {
        triedb_.finalize(block_number, block_id);
    }

    virtual void update_verified_block(uint64_t const block_number) override
    {
        triedb_.update_verified_block(block_number);
    }

    virtual void update_voted_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        triedb_.update_voted_metadata(block_number, block_id);
    }

    virtual void update_proposed_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        triedb_.update_proposed_metadata(block_number, block_id);
    }

    virtual void commit(
        bytes32_t const &block_id, CommitBuilder &builder,
        BlockHeader const &header, StateDeltas const &state_deltas,
        std::function<void(BlockHeader &)> populate_header_fn) override
    {
        triedb_.commit(
            block_id, builder, header, state_deltas, populate_header_fn);
    }

    virtual BlockHeader read_eth_header() override
    {
        return triedb_.read_eth_header();
    }

    virtual bytes32_t state_root() override
    {
        return triedb_.state_root();
    }

    virtual bytes32_t receipts_root() override
    {
        return triedb_.receipts_root();
    }

    virtual bytes32_t transactions_root() override
    {
        return triedb_.transactions_root();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        return triedb_.withdrawals_root();
    }

    virtual std::string print_stats() override
    {
        return triedb_.print_stats();
    }

    virtual uint64_t get_block_number() const override
    {
        return triedb_.get_block_number();
    }
};

struct MonadRunloopImpl
{
    std::unique_ptr<MonadChain> chain;
    fs::path ledger_dir;
    AccountOverrideMap account_override;
    mpt::Db raw_db;
    mpt::Db secondary_raw_db;
    TrieDb triedb;
    TrieDb secondary_triedb;
    MonadRunloopTrieDb runloop_db;
    MonadRunloopTrieDb secondary_runloop_db;
    vm::VM vm;
    BlockHashBufferFinalized block_hash_buffer;
    fiber::PriorityPool priority_pool;
    uint64_t block_num;
    bool is_first_run;

    MonadRunloopImpl(
        uint64_t chain_id, char const *ledger_path, char const *db_path);
};

mpt::Db get_secondary_raw_db(mpt::Db &db)
{
    if (db.timeline_active(mpt::timeline_id::secondary)) {
        auto db2 =
            db.open_secondary_timeline(std::make_unique<MonadOnDiskMachine>());
        MONAD_ASSERT(db2.has_value());
        return std::move(*db2);
    }
    return db.activate_secondary_timeline(
        std::make_unique<MonadOnDiskMachine>());
}

MonadRunloopImpl::MonadRunloopImpl(
    uint64_t const chain_id, char const *const ledger_path,
    char const *const db_path)
    : chain{monad_chain_from_chain_id(chain_id)}
    , ledger_dir{ledger_path}
    , raw_db{std::make_unique<OnDiskMachine>(), mpt::OnDiskDbConfig{.append = true, .compaction = true, .rewind_to_latest_finalized = true, .rd_buffers = 8192, .wr_buffers = 32, .uring_entries = 128, .sq_thread_cpu = sq_thread_cpu, .dbname_paths = {fs::path{db_path}}}}
    , secondary_raw_db{get_secondary_raw_db(raw_db)}
    , triedb{raw_db, /*enable_multiblock_cache=*/true}
    , secondary_triedb{secondary_raw_db}
    , runloop_db{triedb, account_override}
    , secondary_runloop_db{secondary_triedb, account_override}
    , vm{}
    , block_hash_buffer{}
    , priority_pool{nthreads, nfibers}
    , is_first_run{true}
{
    MONAD_ASSERT(triedb.is_page_encoded() == false);
    MONAD_ASSERT(secondary_triedb.is_page_encoded() == true);
    if (triedb.get_root() == nullptr) {
        LOG_INFO("loading from genesis");
        GenesisState const genesis_state = chain->get_genesis_state();
        load_genesis_state(genesis_state, triedb);
        load_genesis_state(genesis_state, secondary_triedb);
    }
    else {
        LOG_INFO("loading from previous DB state");
    }

    uint64_t const init_block_num = triedb.get_block_number();
    block_num = init_block_num + 1;

    LOG_INFO("Init block number = {}", init_block_num);

    mpt::AsyncIOContext io_ctx{mpt::ReadOnlyOnDiskDbConfig{
        .sq_thread_cpu = sq_thread_cpu, .dbname_paths = {fs::path{db_path}}}};
    mpt::Db rodb{io_ctx};
    bool const have_headers =
        init_block_hash_buffer_from_triedb(rodb, block_num, block_hash_buffer);
    if (!have_headers) {
        BlockDb block_db{ledger_path};
        MONAD_ASSERT(chain_id == mainnet_chain_id);
        MONAD_ASSERT(init_block_hash_buffer_from_blockdb(
            block_db, block_num, block_hash_buffer));
    }
}

MonadRunloopImpl *to_impl(MonadRunloop *const x)
{
    return reinterpret_cast<MonadRunloopImpl *>(x);
}

MonadRunloop *from_impl(MonadRunloopImpl *const x)
{
    return reinterpret_cast<MonadRunloop *>(x);
}

Address to_address(MonadRunloopAddress const *const a)
{
    return std::bit_cast<Address>(*a);
}

uint256_t to_uint256(MonadRunloopWord const *const x)
{
    return load_be<uint256_t>(*x);
}

class RunloopOverrideMethods : public RunloopMonadOverrideMethods
{
private:
    bool is_first_run_;
    AccountOverrideMap &account_override_;
    MonadRunloopTrieDb &runloop_db_;

public:
    RunloopOverrideMethods(
        bool is_first_run, AccountOverrideMap &account_override,
        MonadRunloopTrieDb &runloop_db)
        : is_first_run_{is_first_run}
        , account_override_{account_override}
        , runloop_db_{runloop_db}
    {
    }

    virtual bool is_first_run() const override
    {
        return is_first_run_;
    }

    virtual void preprocess_state_deltas(
        std::unique_ptr<StateDeltas> *state_deltas) const override
    {
        auto new_sds = std::make_unique<StateDeltas>();
        for (auto const &[a, sd] : **state_deltas) {
            auto over_it = account_override_.find(a);
            if (over_it == account_override_.end()) {
                new_sds->emplace(a, sd);
            }
            else {
                auto const orig = runloop_db_.read_underlying_account(a);
                auto const orig_delta = [&] {
                    if (orig) {
                        return orig;
                    }
                    return std::make_optional<Account>();
                }();
                AccountDelta const ad{orig_delta, sd.account.second};
                StateDelta new_sd{ad, sd.storage};
                new_sds->emplace(a, new_sd);
                account_override_.erase(over_it);
            }
        }
        for (auto const &[a, over] : account_override_) {
            auto const orig_acct = runloop_db_.read_underlying_account(a);
            auto const orig_delta = [&] {
                if (orig_acct) {
                    return orig_acct;
                }
                return std::make_optional<Account>();
            }();
            auto over_delta = orig_delta;
            over_delta->balance = over.balance;
            AccountDelta const ad{orig_delta, over_delta};
            StateDelta const sd{ad, {}};
            new_sds->emplace(a, sd);
        }
        account_override_.clear();
        *state_deltas = std::move(new_sds);
    }
};

MONAD_ANONYMOUS_NAMESPACE_END

extern "C" MonadRunloop *monad_runloop_new(
    uint64_t const chain_id, char const *const ledger_path,
    char const *const db_path)
{
    static bool is_quill_running;
    if (!is_quill_running) {
        init_root_logger(log_level);
        is_quill_running = true;
    }
    return from_impl(new MonadRunloopImpl{chain_id, ledger_path, db_path});
}

extern "C" void monad_runloop_delete(MonadRunloop *const runloop)
{
    delete to_impl(runloop);
}

extern "C" void
monad_runloop_run(MonadRunloop *const pre_runloop, uint64_t const nblocks)
try {
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);

    auto const block_num_before = runloop->block_num;

    RunloopOverrideMethods override_methods{
        runloop->is_first_run, runloop->account_override, runloop->runloop_db};
    RunloopMonadOverride runloop_override{&override_methods};

    sig_atomic_t const stop = 0;
    auto const result = runloop_monad(
        *runloop->chain,
        runloop->ledger_dir,
        runloop->raw_db,
        runloop->runloop_db,
        runloop->vm,
        runloop->block_hash_buffer,
        runloop->priority_pool,
        runloop->block_num,
        runloop->block_num + nblocks - 1,
        stop,
        /* enable_tracing = */ false,
        &runloop->secondary_runloop_db,
        runloop_override);

    runloop->is_first_run = false;

    auto const block_num_after = runloop->block_num;

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
    MonadRunloop *const pre_runloop, MonadRunloopAddress const *const raw_addr,
    MonadRunloopWord const *const raw_bal)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    auto const addr = to_address(raw_addr);
    auto const bal = to_uint256(raw_bal);
    runloop->account_override[addr].balance = bal;
}

extern "C" void monad_runloop_get_balance(
    MonadRunloop *const pre_runloop, MonadRunloopAddress const *const raw_addr,
    MonadRunloopWord *const result_balance)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    uint256_t bal;
    auto const addr = to_address(raw_addr);
    auto const over_it = runloop->account_override.find(addr);
    if (over_it != runloop->account_override.end()) {
        bal = over_it->second.balance;
    }
    else {
        auto const acct = runloop->triedb.read_account(addr);
        if (acct) {
            bal = acct->balance;
        }
    }
    store_be(result_balance->bytes, bal);
}

extern "C" void monad_runloop_get_primary_state_root(
    MonadRunloop *const pre_runloop, MonadRunloopWord *const result_state_root)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    *result_state_root =
        std::bit_cast<MonadRunloopWord>(runloop->triedb.state_root());
}

extern "C" void monad_runloop_get_secondary_state_root(
    MonadRunloop *const pre_runloop, MonadRunloopWord *const result_state_root)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    *result_state_root = std::bit_cast<MonadRunloopWord>(
        runloop->secondary_runloop_db.state_root());
}

extern "C" void monad_runloop_dump(MonadRunloop *const pre_runloop)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    std::cout << runloop->triedb.to_json().dump(4) << std::endl;
}
