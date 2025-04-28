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
#include <span>
#include <stdio.h>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;
using namespace monad::test_statesync;

void statesync_send_request(
    monad_statesync_client *const client, monad_sync_request const rq)
{
    if (client->mask & (1ull << (rq.prefix % 64))) {
        monad::test_statesync::statesync_send_request(client, rq);
    }
}

extern "C" int
LLVMFuzzerTestOneInput(uint8_t const *const data, size_t const size)
{
    if (size < sizeof(uint64_t)) {
        return -1;
    }

    fprintf(stderr, "size=%zu\n", size);

    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Error);
    std::filesystem::path const cdbname{tmp_dbname()};
    char const *const cdbname_str = cdbname.c_str();
    monad_statesync_client client;
    monad_statesync_client_context *const cctx =
        monad_statesync_client_context_create(
            &cdbname_str,
            1,
            "",
            static_cast<unsigned>(get_nprocs() - 1),
            &client,
            &::statesync_send_request);
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
    monad_statesync_server_network net{
        .client = &client, .cctx = cctx, .buf = {}};
    for (size_t i = 0; i < monad_statesync_client_prefixes(); ++i) {
        monad_statesync_client_handle_new_peer(
            cctx, i, monad_statesync_version());
    }
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
    while (raw.size() >= sizeof(uint64_t)) {
        StateDeltas deltas;
        uint64_t const n = unaligned_load<uint64_t>(raw.data());
        raw = raw.subspan(sizeof(uint64_t));
        Incarnation const incarnation{stdb.get_block_number(), 0};
        switch (n % 6) {
        case 0:
            new_account(deltas, state, incarnation, n);
            break;
        case 1:
            update_account(deltas, state, stdb, n, incarnation);
            break;
        case 2:
            remove_account(deltas, state, stdb);
            break;
        case 3:
            new_storage(deltas, state, stdb, n);
            break;
        case 4:
            update_storage(deltas, state, stdb, n);
            break;
        case 5:
            remove_storage(deltas, state, stdb, n);
            break;
        }
        client.mask = raw.size() < sizeof(uint64_t)
                          ? std::numeric_limits<uint64_t>::max()
                          : n;
        hdr.number = stdb.get_block_number() + 1;
        MONAD_ASSERT(hdr.number > 0);
        sctx->set_block_and_round(hdr.number - 1);
        sctx->commit(
            deltas, {}, MonadConsensusBlockHeader::from_eth_header(hdr));
        sctx->finalize(hdr.number, hdr.number);
        auto const rlp = rlp::encode_block_header(sctx->read_eth_header());
        monad_statesync_client_handle_target(cctx, rlp.data(), rlp.size());
        while (!client.rqs.empty()) {
            monad_statesync_server_run_once(server);
        }
    }
    quill::flush();
    MONAD_ASSERT(monad_statesync_client_has_reached_target(cctx));
    MONAD_ASSERT(monad_statesync_client_finalize(cctx));

    monad_statesync_client_context_destroy(cctx);
    monad_statesync_server_destroy(server);
    std::filesystem::remove(cdbname);
    std::filesystem::remove(sdbname);

    return 0;
}
