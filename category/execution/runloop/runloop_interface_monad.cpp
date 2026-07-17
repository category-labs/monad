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
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/block_hash_buffer/util.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/monad/chain/eest_net.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/execution/runloop/runloop_interface_monad.h>
#include <category/execution/runloop/runloop_monad.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <evmc/hex.hpp>

#include <algorithm>
#include <bit>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <memory>
#include <sstream>
#include <string>
#include <thread>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

using namespace monad;
namespace fs = std::filesystem;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

// Pin the io_uring SQPOLL thread outside the worker CPUs where it
// can; fall back to the highest available CPU on smaller hosts
// (IORING_SETUP_SQ_AFF rejects an out-of-range CPU with EINVAL).
unsigned const sq_thread_cpu =
    std::min(7u, std::max(1u, std::thread::hardware_concurrency()) - 1u);
quill::LogLevel const log_level = quill::LogLevel::Info;
unsigned const nthreads = 4;
unsigned const nfibers = 256;

struct MonadRunloopImpl
{
    std::unique_ptr<MonadChain> chain;
    fs::path ledger_dir;
    mpt::Db raw_db;
    TrieDb triedb;
    // Dual-db migration: a page-encoded secondary timeline (if activated
    // on the db) runs alongside the slot-encoded primary so a
    // MONAD_NINE->MONAD_NEXT transition can cross the page-encoding
    // boundary. Empty for single-encoding (pure pre-MIP-8 or pure MIP-8).
    std::optional<mpt::Db> secondary_raw_db;
    std::optional<TrieDb> secondary_triedb;
    vm::VM vm;
    BlockHashBufferFinalized block_hash_buffer;
    fiber::PriorityPool priority_pool;
    uint64_t block_num;
    bool is_first_run;

    MonadRunloopImpl(
        std::unique_ptr<MonadChain> chain, char const *ledger_path,
        char const *db_path);
};

MonadRunloopImpl::MonadRunloopImpl(
    std::unique_ptr<MonadChain> chain_arg, char const *ledger_path,
    char const *db_path)
    : chain{std::move(chain_arg)}
    , ledger_dir{ledger_path}
    , raw_db{[&] {
        // The on-disk Db ctor constructs the StateMachine from the
        // persisted state_machine_kind via these registries, so they must
        // be registered first.
        register_ethereum_state_machines();
        register_monad_state_machines();
        return mpt::Db{mpt::OnDiskDbConfig{
            .append = true,
            .compaction = true,
            .rewind_to_latest_finalized = true,
            .rd_buffers = 8192,
            .wr_buffers = 32,
            .uring_entries = 128,
            .sq_thread_cpu = sq_thread_cpu,
            .dbname_paths = {fs::path{db_path}}}};
    }()}
    , triedb{raw_db, true}
    , vm{}
    , block_hash_buffer{}
    , priority_pool{nthreads, nfibers}
    , block_num{1}
    , is_first_run{true}
{
    // Open the page-encoded secondary timeline for dual-write migration
    // mode (slot primary + page secondary), if it was activated on the db.
    bool const secondary_active =
        raw_db.timeline_active(mpt::timeline_id::secondary);
    LOG_INFO("dual-db: secondary timeline active = {}", secondary_active);
    if (secondary_active) {
        secondary_raw_db = raw_db.open_secondary_timeline();
        MONAD_ASSERT(secondary_raw_db.has_value());
        secondary_triedb.emplace(*secondary_raw_db);
        MONAD_ASSERT(
            secondary_triedb->is_page_encoded(),
            "secondary timeline must be page-encoded");
        LOG_INFO("dual-db: opened page-encoded secondary timeline");
    }

    if (triedb.get_root() == nullptr) {
        LOG_INFO("loading from genesis");
        GenesisState const genesis_state = chain->get_genesis_state();
        load_genesis_state(genesis_state, triedb);
        // Seed the secondary with the same genesis so dual-writes build on
        // a consistent page-encoded base.
        if (secondary_triedb.has_value()) {
            load_genesis_state(genesis_state, *secondary_triedb);
        }
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
        rodb, start_block_num, block_hash_buffer);
    MONAD_ASSERT(have_headers);
}

MonadRunloopImpl *to_impl(MonadRunloop *x)
{
    return reinterpret_cast<MonadRunloopImpl *>(x);
}

MonadRunloop *from_impl(MonadRunloopImpl *x)
{
    return reinterpret_cast<MonadRunloop *>(x);
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_ANONYMOUS_NAMESPACE_BEGIN

void monad_runloop_init_logging()
{
    init_root_logger(log_level);
}

MONAD_ANONYMOUS_NAMESPACE_END

extern "C" MonadRunloop *monad_runloop_new_eest(
    char const *ledger_path, char const *db_path,
    char const *genesis_alloc_json, char const *genesis_block_rlp_hex,
    char const *revision_schedule)
{
    monad_runloop_init_logging();
    MONAD_ASSERT(genesis_alloc_json != nullptr);
    MONAD_ASSERT(genesis_block_rlp_hex != nullptr);
    MONAD_ASSERT(revision_schedule != nullptr);
    auto const genesis_block_rlp =
        evmc::from_hex(std::string_view{genesis_block_rlp_hex});
    MONAD_ASSERT(genesis_block_rlp.has_value());
    byte_string_view genesis_block_rlp_view{
        genesis_block_rlp->data(), genesis_block_rlp->size()};
    auto const genesis_block = rlp::decode_block(genesis_block_rlp_view);
    MONAD_ASSERT(!genesis_block.has_error());

    // Parse "<revision>:<from timestamp>,..." into the schedule.
    EestNetRevisionSchedule schedule;
    std::istringstream stream{revision_schedule};
    std::string entry;
    while (std::getline(stream, entry, ',')) {
        auto const sep = entry.find(':');
        MONAD_ASSERT(sep != std::string::npos);
        auto const revision = std::stoul(entry.substr(0, sep));
        MONAD_ASSERT(revision <= MONAD_NEXT);
        auto const from_timestamp = std::stoull(entry.substr(sep + 1));
        schedule.emplace_back(
            from_timestamp, static_cast<monad_revision>(revision));
    }

    return from_impl(new MonadRunloopImpl{
        std::make_unique<EestNet>(
            std::string{genesis_alloc_json},
            genesis_block.assume_value().header,
            std::move(schedule)),
        ledger_path,
        db_path});
}

extern "C" void monad_runloop_delete(MonadRunloop *runloop)
{
    delete to_impl(runloop);
}

extern "C" void monad_runloop_run(MonadRunloop *pre_runloop, uint64_t nblocks)
try {
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);

    auto const block_num_before = runloop->block_num;

    sig_atomic_t const stop = 0;
    auto const result = runloop_monad(
        *runloop->chain,
        runloop->ledger_dir,
        runloop->raw_db,
        runloop->triedb,
        runloop->vm,
        runloop->block_hash_buffer,
        runloop->priority_pool,
        runloop->block_num,
        runloop->block_num + nblocks - 1,
        stop,
        /* enable_tracing = */ false,
        /* secondary_db = */ runloop->secondary_triedb.has_value()
            ? &*runloop->secondary_triedb
            : nullptr,
        /* is_first_run = */ runloop->is_first_run);

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

extern "C" void monad_runloop_get_state_root(
    MonadRunloop *pre_runloop, MonadRunloopWord *result_state_root)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    // In dual-db migration mode the canonical final state_root is the
    // page-encoded secondary's (transition fixtures end post-fork in
    // MONAD_NEXT); the slot primary holds the pre-fork-encoded root.
    bytes32_t const root = runloop->secondary_triedb.has_value()
                               ? runloop->secondary_triedb->state_root()
                               : runloop->triedb.state_root();
    *result_state_root = std::bit_cast<MonadRunloopWord>(root);
}

extern "C" char *monad_runloop_dump_json(MonadRunloop *pre_runloop)
{
    MonadRunloopImpl *const runloop = to_impl(pre_runloop);
    auto const json = runloop->triedb.to_json().dump();
    return strdup(json.c_str());
}

extern "C" void monad_runloop_free_string(char *str)
{
    free(str);
}
