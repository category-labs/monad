#include <monad/config.hpp>
#include <monad/core/address.hpp>
#include <monad/core/assert.h>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_messages.h>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>
#include <monad/statesync/statesync_version.h>
#include <monad/statesync/test/fuzz_statesync.hpp>

#include <ankerl/unordered_dense.h>
#include <quill/Quill.h>

#include <cstdint>
#include <deque>
#include <limits>
#include <optional>
#include <random>
#include <span>
#include <stdio.h>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test_statesync;

struct config
{
    uint16_t num_inserts[2];
    uint16_t num_updates;
    uint16_t num_deletes;
    uint16_t num_storage_inserts[2];
    uint16_t num_storage_updates;
    uint16_t num_storage_deletes;
    uint8_t restore_prefix_mask[2];
    uint64_t seed;
};

// Generate some data, run statesync to an empty database.
// After transfer complete, restore random prefixes and rerun requests.
// Generate some more data including updates and deletes, rerun statesync
// with prefix restore.

extern "C" int
LLVMFuzzerTestOneInput(uint8_t const *const data, size_t const size)
{
    if (size != sizeof(config)) {
        return -1;
    }

    config const *const cfg = reinterpret_cast<config const *>(data);

    if (cfg->num_inserts[0] == 0) {
        return -1;
    }

    fprintf(
        stderr,
        "inserts =%u/%u updates=%u deletes=%u storage_inserts=%u/%u "
        "storage_updates=%u storage_deletes=%u\n",
        cfg->num_inserts[0],
        cfg->num_inserts[1],
        cfg->num_updates,
        cfg->num_deletes,
        cfg->num_storage_inserts[0],
        cfg->num_storage_inserts[1],
        cfg->num_storage_updates,
        cfg->num_storage_deletes);

    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Error);
    std::filesystem::path const cdbname{tmp_dbname()};
    char const *const cdbname_str = cdbname.c_str();
    std::filesystem::path sdbname{tmp_dbname()};
    OnDiskMachine machine;
    mpt::Db sdb{
        machine, OnDiskDbConfig{.append = true, .dbname_paths = {sdbname}}};
    TrieDb stdb{sdb};
    std::unique_ptr<monad_statesync_server_context> sctx =
        std::make_unique<monad_statesync_server_context>(stdb);
    mpt::AsyncIOContext io_ctx{ReadOnlyOnDiskDbConfig{.dbname_paths{sdbname}}};
    mpt::Db ro{io_ctx};
    sctx->ro = &ro;
    monad_statesync_server_network net{};
    monad_statesync_server *const server = monad_statesync_server_create(
        sctx.get(),
        &net,
        &statesync_server_recv,
        &statesync_server_send_upsert,
        &statesync_server_send_done);

    std::span<uint8_t const> raw{data, size};
    State state{};

    BlockHeader hdr{.number = 0};
    sctx->commit(
        StateDeltas{}, Code{}, MonadConsensusBlockHeader::from_eth_header(hdr));
    sctx->finalize(0, 0);

    std::mt19937_64 gen(cfg->seed);
    std::uniform_int_distribution<uint64_t> dist(
        0, std::numeric_limits<uint64_t>::max());

    {
        StateDeltas deltas;
        for (uint16_t i = 0; i < cfg->num_inserts[0]; ++i) {
            new_account(
                deltas,
                state,
                Incarnation{stdb.get_block_number(), 0},
                dist(gen));
        }
        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
    }

    {
        StateDeltas deltas;
        for (uint16_t i = 0; i < cfg->num_storage_inserts[0]; ++i) {
            new_storage(deltas, state, stdb, dist(gen));
        }

        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
    }

    {
        monad_statesync_client client;
        monad_statesync_client_context *cctx =
            monad_statesync_client_context_create(
                &cdbname_str,
                1,
                "",
                static_cast<unsigned>(get_nprocs() - 1),
                &client,
                &statesync_send_request);

        net.cctx = cctx;
        net.client = &client;

        auto const rlp = rlp::encode_block_header(sctx->read_eth_header());
        for (size_t i = 0; i < monad_statesync_client_prefixes(); ++i) {
            monad_statesync_client_handle_new_peer(
                cctx, i, monad_statesync_version());
        }
        monad_statesync_client_handle_target(cctx, rlp.data(), rlp.size());
        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
        quill::flush();
        MONAD_ASSERT(monad_statesync_client_has_reached_target(cctx));
        for (size_t i = 0; i < monad_statesync_client_prefixes(); ++i) {
            if (cfg->restore_prefix_mask[0] & (1 << i)) {
                monad_statesync_client_restore_prefix(cctx, i);
            }
        }
        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
        MONAD_ASSERT(monad_statesync_client_has_reached_target(cctx));
        MONAD_ASSERT(monad_statesync_client_finalize(cctx));

        monad_statesync_client_context_destroy(cctx);
    }

    {
        StateDeltas deltas;
        for (uint16_t i = 0; i < cfg->num_inserts[1]; ++i) {
            new_account(
                deltas,
                state,
                Incarnation{stdb.get_block_number(), 0},
                dist(gen));
        }
        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
    }

    {
        StateDeltas deltas;
        for (uint16_t i = 0; i < cfg->num_storage_inserts[1]; ++i) {
            new_storage(deltas, state, stdb, dist(gen));
        }

        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
    }
    {
        StateDeltas deltas;
        for (uint16_t i = 0; i < cfg->num_storage_updates; ++i) {
            update_storage(deltas, state, stdb, dist(gen));
        }

        for (uint16_t i = 0; i < cfg->num_updates; ++i) {
            update_account(
                deltas,
                state,
                stdb,
                dist(gen),
                Incarnation{stdb.get_block_number(), 0});
        }
        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
    }

    {
        StateDeltas deltas;
        for (uint16_t i = 0; i < cfg->num_deletes; ++i) {
            remove_account(deltas, state, stdb);
        }

        for (uint16_t i = 0; i < cfg->num_storage_deletes; ++i) {
            remove_storage(deltas, state, stdb, dist(gen));
        }

        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
    }

    {
        monad_statesync_client client;
        monad_statesync_client_context *cctx =
            monad_statesync_client_context_create(
                &cdbname_str,
                1,
                "",
                static_cast<unsigned>(get_nprocs() - 1),
                &client,
                &statesync_send_request);

        net.cctx = cctx;
        net.client = &client;

        auto const rlp = rlp::encode_block_header(sctx->read_eth_header());
        for (size_t i = 0; i < monad_statesync_client_prefixes(); ++i) {
            monad_statesync_client_handle_new_peer(
                cctx, i, monad_statesync_version());
        }
        monad_statesync_client_handle_target(cctx, rlp.data(), rlp.size());

        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
        quill::flush();
        MONAD_ASSERT(monad_statesync_client_has_reached_target(cctx));

        for (size_t i = 0; i < monad_statesync_client_prefixes(); ++i) {
            if (cfg->restore_prefix_mask[1] & (1 << i)) {
                monad_statesync_client_restore_prefix(cctx, i);
            }
        }
        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
        MONAD_ASSERT(monad_statesync_client_has_reached_target(cctx));
        MONAD_ASSERT(monad_statesync_client_finalize(cctx));

        monad_statesync_client_context_destroy(cctx);
    }
    monad_statesync_server_destroy(server);
    std::filesystem::remove(cdbname);
    std::filesystem::remove(sdbname);

    return 0;
}
