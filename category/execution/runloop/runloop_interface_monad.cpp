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
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/db/block_db.hpp>
#include <category/execution/ethereum/db/db_cache.hpp>
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

#include <quill/LogLevel.h>
#include <quill/Quill.h>
#include <quill/handlers/FileHandler.h>

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

struct MonadRunloopTrieDb : public Db
{
    AccountOverrideMap account_override;
    Db &triedb;

    MonadRunloopTrieDb(Db &db)
        : triedb{db}
    {
    }

    std::optional<Account> read_underlying_account(Address const &address)
    {
        return triedb.read_account(address);
    }

    virtual std::optional<Account> read_account(Address const &address) override
    {
        auto acct = triedb.read_account(address);
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
        return triedb.read_storage(address, incarnation, key);
    }

    virtual vm::SharedIntercode read_code(bytes32_t const &code_hash) override
    {
        return triedb.read_code(code_hash);
    }

    virtual void set_block_and_prefix(
        uint64_t const block_number,
        bytes32_t const &block_id = bytes32_t{}) override
    {
        triedb.set_block_and_prefix(block_number, block_id);
    }

    virtual void
    finalize(uint64_t const block_number, bytes32_t const &block_id) override
    {
        triedb.finalize(block_number, block_id);
    }

    virtual void update_verified_block(uint64_t const block_number) override
    {
        triedb.update_verified_block(block_number);
    }

    virtual void update_voted_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        triedb.update_voted_metadata(block_number, block_id);
    }

    virtual void update_proposed_metadata(
        uint64_t const block_number, bytes32_t const &block_id) override
    {
        triedb.update_proposed_metadata(block_number, block_id);
    }

    virtual void commit(
        bytes32_t const &block_id, CommitBuilder &builder,
        BlockHeader const &header, StateDeltas const &state_deltas,
        std::function<void(BlockHeader &)> populate_header_fn) override
    {
        triedb.commit(
            block_id, builder, header, state_deltas, populate_header_fn);
    }

    virtual BlockHeader read_eth_header() override
    {
        return triedb.read_eth_header();
    }

    virtual bytes32_t state_root() override
    {
        return triedb.state_root();
    }

    virtual bytes32_t receipts_root() override
    {
        return triedb.receipts_root();
    }

    virtual bytes32_t transactions_root() override
    {
        return triedb.transactions_root();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        return triedb.withdrawals_root();
    }

    virtual std::string print_stats() override
    {
        return triedb.print_stats();
    }

    virtual uint64_t get_block_number() const override
    {
        return triedb.get_block_number();
    }
};

struct MonadRunloopImpl
{
    std::unique_ptr<MonadChain> chain;
    fs::path ledger_dir;
    OnDiskMachine db_machine;
    mpt::Db raw_db;
    TrieDb triedb;
    MonadRunloopTrieDb runloop_db;
    DbCache db_cache;
    vm::VM vm;
    BlockHashBufferFinalized block_hash_buffer;
    fiber::PriorityPool priority_pool;
    uint64_t block_num;
    bool is_first_run;

    MonadRunloopImpl(
        uint64_t chain_id, char const *ledger_path, char const *db_path);
};

MonadRunloopImpl::MonadRunloopImpl(
    uint64_t const chain_id, char const *const ledger_path,
    char const *const db_path)
    : chain{monad_chain_from_chain_id(chain_id)}
    , ledger_dir{ledger_path}
    , db_machine{}
    , raw_db{db_machine, mpt::OnDiskDbConfig{.append = true, .compaction = true, .rewind_to_latest_finalized = true, .rd_buffers = 8192, .wr_buffers = 32, .uring_entries = 128, .sq_thread_cpu = sq_thread_cpu, .dbname_paths = {fs::path{db_path}}}}
    , triedb{raw_db}
    , runloop_db{triedb}
    , db_cache{runloop_db}
    , vm{}
    , block_hash_buffer{}
    , priority_pool{nthreads, nfibers}
    , is_first_run{true}
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
    return intx::be::load<uint256_t>(*x);
}

class RunloopConfig : public RunloopMonadTestConfig<true>
{
private:
    bool is_first_run_;
    MonadRunloopTrieDb &runloop_db_;

public:
    RunloopConfig(bool is_first_run, MonadRunloopTrieDb &runloop_db)
        : is_first_run_{is_first_run}
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
        auto &account_override = runloop_db_.account_override;
        auto new_sds = std::make_unique<StateDeltas>();
        for (auto const &[a, sd] : **state_deltas) {
            auto over_it = account_override.find(a);
            if (over_it == account_override.end()) {
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
                account_override.erase(over_it);
            }
        }
        for (auto const &[a, over] : account_override) {
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
        account_override.clear();
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
        auto stdout_handler = quill::stdout_handler();
        quill::Config quill_cfg;
        quill_cfg.default_handlers.emplace_back(stdout_handler);
        quill::configure(quill_cfg);
        quill::start(true);
        quill::get_root_logger()->set_log_level(log_level);
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

    RunloopConfig config{runloop->is_first_run, runloop->runloop_db};

    sig_atomic_t const stop = 0;
    auto const result = runloop_monad<true>(
        *runloop->chain,
        runloop->ledger_dir,
        runloop->raw_db,
        runloop->db_cache,
        runloop->vm,
        runloop->block_hash_buffer,
        runloop->priority_pool,
        runloop->block_num,
        runloop->block_num + nblocks - 1,
        stop,
        /* enable_tracing = */ false,
        config);

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
    auto const old_acct = runloop->db_cache.read_account(addr);
    auto const bal = to_uint256(raw_bal);
    auto const new_acct = [&] -> std::optional<Account> {
        if (old_acct) {
            auto a = old_acct;
            a->balance = bal;
            return a;
        }
        auto a = std::make_optional<Account>();
        a->balance = bal;
        return a;
    }();
    runloop->db_cache.insert_in_lru_caches(
        {{addr, {{old_acct, new_acct}, {}}}});
    runloop->runloop_db.account_override[addr].balance = bal;
}

extern "C" void monad_runloop_get_balance(
    MonadRunloop *const pre_runloop, MonadRunloopAddress const *const raw_addr,
    MonadRunloopWord *const result_balance)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    auto const addr = to_address(raw_addr);
    auto const acct = runloop->db_cache.read_account(addr);
    uint256_t bal;
    if (acct) {
        bal = acct->balance;
    }
    intx::be::store(result_balance->bytes, bal);
}

extern "C" void monad_runloop_get_state_root(
    MonadRunloop *const pre_runloop, MonadRunloopWord *const result_state_root)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    *result_state_root =
        std::bit_cast<MonadRunloopWord>(runloop->db_cache.state_root());
}

extern "C" void monad_runloop_dump(MonadRunloop *const pre_runloop)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    std::cout << runloop->triedb.to_json().dump(4) << std::endl;
}
