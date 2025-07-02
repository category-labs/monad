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

struct monad_statesync_client
{
    std::deque<monad_sync_request> rqs;
    uint64_t mask;
};

struct monad_statesync_server_network
{
    monad_statesync_client *client;
    monad_statesync_client_context *cctx;
    byte_string buf;
};

void statesync_send_request(
    monad_statesync_client *const client, monad_sync_request const rq)
{
    if (client->mask & (1ull << (rq.prefix % 64))) {
        client->rqs.push_back(rq);
    }
}

ssize_t statesync_server_recv(
    monad_statesync_server_network *const net, unsigned char *const buf,
    size_t const len)
{
    if (len == 1) {
        constexpr auto MSG_TYPE = SYNC_TYPE_REQUEST;
        std::memcpy(buf, &MSG_TYPE, 1);
    }
    else {
        MONAD_ASSERT(len == sizeof(monad_sync_request));
        std::memcpy(buf, &net->client->rqs.front(), sizeof(monad_sync_request));
        net->client->rqs.pop_front();
    }
    return static_cast<ssize_t>(len);
}

void statesync_server_send_upsert(
    monad_statesync_server_network *const net, monad_sync_type const type,
    unsigned char const *const v1, uint64_t const size1,
    unsigned char const *const v2, uint64_t const size2)
{
    net->buf.clear();
    if (v1 != nullptr) {
        net->buf.append(v1, size1);
    }
    if (v2 != nullptr) {
        net->buf.append(v2, size2);
    }
    MONAD_ASSERT(monad_statesync_client_handle_upsert(
        net->cctx, 0, type, net->buf.data(), net->buf.size()));
}

void statesync_server_send_done(
    monad_statesync_server_network *const net, monad_sync_done const done)
{
    monad_statesync_client_handle_done(net->cctx, done);
}

MONAD_NAMESPACE_BEGIN

namespace
{
    struct Range
    {
        uint64_t begin{0};
        uint64_t end{0};
    };

    struct State : Range
    {
        ankerl::unordered_dense::segmented_map<uint64_t, Range> storage;
    };

    void new_account(
        StateDeltas &deltas, State &state, Incarnation const incarnation,
        uint64_t const n)
    {
        bool const success = deltas.emplace(
            Address{state.end},
            StateDelta{
                .account = AccountDelta{
                    std::nullopt,
                    Account{.balance = n, .incarnation = incarnation}}});
        MONAD_ASSERT(success);
        ++state.end;
    }

    void update_account(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n,
        Incarnation const incarnation)
    {
        if (state.begin == state.end) {
            return;
        }
        uint64_t const addr = (n % (state.end - state.begin)) + state.begin;
        auto const orig = db.read_account(Address{addr});
        MONAD_ASSERT(orig.has_value());
        bool const reincarnate = (n % 10) == 1;
        bool const success = deltas.emplace(
            Address{addr},
            StateDelta{
                .account = AccountDelta{
                    orig,
                    Account{
                        .balance = n,
                        .incarnation = reincarnate
                                           ? incarnation
                                           : orig.value().incarnation}}});
        MONAD_ASSERT(success);
        if (reincarnate) {
            state.storage.erase(addr);
        }
    }

    void remove_account(StateDeltas &deltas, State &state, TrieDb &db)
    {
        if (state.begin == state.end) {
            return;
        }
        Address const addr{state.begin};
        bool const success = deltas.emplace(
            addr,
            StateDelta{
                .account = AccountDelta{
                    db.read_account(Address{state.begin}), std::nullopt}});
        MONAD_ASSERT(success);
        state.storage.erase(state.begin);
        ++state.begin;
    }

    void
    new_storage(StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n)
    {
        if (state.begin == state.end) {
            return;
        }
        uint64_t const addr = n % (state.end - state.begin) + state.begin;
        auto const orig = db.read_account(Address{addr});
        MONAD_ASSERT(orig.has_value());
        StateDeltas::accessor it;
        bytes32_t const end{state.storage[addr].end++};
        bool success = deltas.emplace(
            it,
            Address{addr},
            StateDelta{
                .account = {orig, orig},
                .storage = StorageDeltas{{end, {bytes32_t{}, bytes32_t{n}}}}});
        MONAD_ASSERT(success);
    }

    void update_storage(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n,
        bool const erase)
    {
        if (state.storage.empty()) {
            return;
        }
        auto const sit = state.storage.begin() +
                         static_cast<unsigned>(n % state.storage.size());
        Address const addr{sit->first};
        auto const orig = db.read_account(addr);
        MONAD_ASSERT(orig.has_value());
        auto &[begin, end] = sit->second;
        MONAD_ASSERT(begin != end);
        bytes32_t const key{erase ? begin : n % (end - begin) + begin};
        bytes32_t const value{erase ? 0 : n};
        auto const sorig = db.read_storage(addr, orig->incarnation, key);
        bool const success = deltas.emplace(
            addr,
            StateDelta{
                .account = {orig, orig},
                .storage = StorageDeltas{{key, {sorig, value}}}});
        MONAD_ASSERT(success && sorig != bytes32_t{});
        if (erase) {
            ++begin;
            if (begin == end) {
                state.storage.erase(sit);
            }
        }
    }

    void update_storage(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n)
    {
        update_storage(deltas, state, db, n, false);
    }

    void remove_storage(
        StateDeltas &deltas, State &state, TrieDb &db, uint64_t const n)
    {
        update_storage(deltas, state, db, n, true);
    }

    std::filesystem::path tmp_dbname()
    {
        std::filesystem::path dbname(
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
            "monad_fuzz_statesync_XXXXXX");
        int const fd = ::mkstemp((char *)dbname.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(
            -1 !=
            ::ftruncate(fd, static_cast<off_t>(8ULL * 1024 * 1024 * 1024)));
        ::close(fd);
        char const *const path = dbname.c_str();
        OnDiskMachine machine;
        mpt::Db const db{
            machine,
            mpt::OnDiskDbConfig{.append = false, .dbname_paths = {path}}};
        return dbname;
    }

}

MONAD_NAMESPACE_END

extern "C" int
LLVMFuzzerTestOneInput(uint8_t const *const data, size_t const size)
{
    if (size < sizeof(uint64_t)) {
        return -1;
    }

    quill::start(false);
    quill::get_root_logger()->set_log_level(quill::LogLevel::Error);
    std::filesystem::path const cdbname{tmp_dbname()};
    char const *const cdbname_str = cdbname.c_str();
    monad_statesync_client client;
    monad_statesync_client_context *const cctx =
        monad_statesync_client_context_create(
            &cdbname_str,
            1,
            static_cast<unsigned>(get_nprocs() - 1),
            &client,
            &statesync_send_request);
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
