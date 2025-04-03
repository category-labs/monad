#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <chrono>
#include <fcntl.h>
#include <mutex>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <thread>
#include <unistd.h>

struct monad_statesync_server
{
    monad_statesync_server_context *context;
    monad_statesync_server_network *net;
    ssize_t (*statesync_server_recv)(
        monad_statesync_server_network *, unsigned char *, size_t);
    void (*statesync_server_send_upsert)(
        struct monad_statesync_server_network *, monad_sync_type,
        unsigned char const *v1, uint64_t size1, unsigned char const *v2,
        uint64_t size2);
    void (*statesync_server_send_done)(
        monad_statesync_server_network *, monad_sync_done);
};

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

byte_string from_prefix(uint64_t const prefix, size_t const n_bytes)
{
    byte_string bytes;
    for (size_t i = 0; i < n_bytes; ++i) {
        bytes.push_back((prefix >> ((n_bytes - i - 1) * 8)) & 0xff);
    }
    return bytes;
}

bool send_deletion(
    monad_statesync_server *const sync, monad_sync_request const &rq,
    monad_statesync_server_context &ctx)
{
    MONAD_ASSERT(
        rq.old_target <= rq.target || rq.old_target == INVALID_BLOCK_ID);

    if (rq.old_target == INVALID_BLOCK_ID) {
        return true;
    }

    auto const fn = [sync, prefix = from_prefix(rq.prefix, rq.prefix_bytes)](
                        Deletion const &deletion) {
        auto const &[addr, key] = deletion;
        auto const hash = keccak256(addr.bytes);
        byte_string_view const view{hash.bytes, sizeof(hash.bytes)};
        if (!view.starts_with(prefix)) {
            return;
        }
        if (!key.has_value()) {
            sync->statesync_server_send_upsert(
                sync->net,
                SYNC_TYPE_UPSERT_ACCOUNT_DELETE,
                reinterpret_cast<unsigned char const *>(&addr),
                sizeof(addr),
                nullptr,
                0);
        }
        else {
            auto const skey = rlp::encode_bytes32_compact(key.value());
            sync->statesync_server_send_upsert(
                sync->net,
                SYNC_TYPE_UPSERT_STORAGE_DELETE,
                reinterpret_cast<unsigned char const *>(&addr),
                sizeof(addr),
                skey.data(),
                skey.size());
        }
    };

    for (uint64_t i = rq.old_target + 1; i <= rq.target; ++i) {
        if (!ctx.deletions.for_each(i, fn)) {
            return false;
        }
    }
    return true;
}

bool statesync_server_handle_request(
    monad_statesync_server *const sync, monad_sync_request const rq)
{
    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    auto *const ctx = sync->context;
    auto &db = *ctx->ro;
    if (rq.prefix < 256 && rq.target > rq.prefix) {
        auto const version = rq.target - rq.prefix - 1;
        auto const root = db.load_root_for_version(version);
        if (!root.is_valid()) {
            return false;
        }
        auto const res = db.find(
            root, concat(FINALIZED_NIBBLE, BLOCKHEADER_NIBBLE), version);
        if (res.has_error() || !res.value().is_valid()) {
            return false;
        }
        auto const &val = res.value().node->value();
        MONAD_ASSERT(!val.empty());
        sync->statesync_server_send_upsert(
            sync->net,
            SYNC_TYPE_UPSERT_HEADER,
            val.data(),
            val.size(),
            nullptr,
            0);
    }

    if (!send_deletion(sync, rq, *ctx)) {
        return false;
    }

    auto const send_upsert = [sync](
                                 monad_sync_type const type,
                                 byte_string_view const v2,
                                 unsigned char const *const v1 = nullptr,
                                 uint64_t const size1 = 0) {
        sync->statesync_server_send_upsert(
            sync->net, type, v1, size1, v2.data(), v2.size());
    };

    auto const bytes = from_prefix(rq.prefix, rq.prefix_bytes);
    [[maybe_unused]] auto const begin = std::chrono::steady_clock::now();
    if (!for_each_state(
            db,
            NibblesView{bytes},
            rq.target,
            rq.from,
            rq.until,
            [send_upsert](byte_string_view const value) {
                send_upsert(SYNC_TYPE_UPSERT_ACCOUNT, value);
            },
            [send_upsert](Address const &addr, byte_string_view const value) {
                send_upsert(
                    SYNC_TYPE_UPSERT_STORAGE,
                    value,
                    reinterpret_cast<unsigned char const *>(&addr),
                    sizeof(addr));
            },
            [send_upsert](byte_string_view const value) {
                send_upsert(SYNC_TYPE_UPSERT_CODE, value);
            })) {
        return false;
    }
    [[maybe_unused]] auto const end = std::chrono::steady_clock::now();

    LOG_INFO(
        "processed request prefix={} prefix_bytes={} target={} from={} "
        "until={} "
        "old_target={} overall={} traverse={}",
        rq.prefix,
        rq.prefix_bytes,
        rq.target,
        rq.from,
        rq.until,
        rq.old_target,
        std::chrono::duration_cast<std::chrono::microseconds>(end - start),
        std::chrono::duration_cast<std::chrono::microseconds>(end - begin));

    return true;
}

void monad_statesync_server_handle_request(
    monad_statesync_server *const sync, monad_sync_request const rq)
{
    auto const success = statesync_server_handle_request(sync, rq);
    if (!success) {
        LOG_INFO(
            "could not handle request prefix={} from={} until={} "
            "old_target={} target={}",
            rq.prefix,
            rq.from,
            rq.until,
            rq.old_target,
            rq.target);
    }
    sync->statesync_server_send_done(
        sync->net,
        monad_sync_done{
            .success = success, .prefix = rq.prefix, .n = rq.until});
}

MONAD_ANONYMOUS_NAMESPACE_END

struct monad_statesync_server *monad_statesync_server_create(
    monad_statesync_server_context *const ctx,
    monad_statesync_server_network *const net,
    ssize_t (*statesync_server_recv)(
        monad_statesync_server_network *, unsigned char *, size_t),
    void (*statesync_server_send_upsert)(
        monad_statesync_server_network *, monad_sync_type,
        unsigned char const *v1, uint64_t size1, unsigned char const *v2,
        uint64_t size2),
    void (*statesync_server_send_done)(
        monad_statesync_server_network *, struct monad_sync_done))
{
    return new monad_statesync_server(monad_statesync_server{
        .context = ctx,
        .net = net,
        .statesync_server_recv = statesync_server_recv,
        .statesync_server_send_upsert = statesync_server_send_upsert,
        .statesync_server_send_done = statesync_server_send_done});
}

void monad_statesync_server_run_once(struct monad_statesync_server *const sync)
{
    unsigned char buf[sizeof(monad_sync_request)];
    if (sync->statesync_server_recv(sync->net, buf, 1) != 1) {
        return;
    }
    MONAD_ASSERT(buf[0] == SYNC_TYPE_REQUEST);
    unsigned char *ptr = buf;
    uint64_t n = sizeof(monad_sync_request);
    while (n != 0) {
        auto const res = sync->statesync_server_recv(sync->net, ptr, n);
        if (res == -1) {
            continue;
        }
        ptr += res;
        n -= static_cast<size_t>(res);
    }
    auto const &rq = unaligned_load<monad_sync_request>(buf);
    monad_statesync_server_handle_request(sync, rq);
}

void monad_statesync_server_destroy(monad_statesync_server *const sync)
{
    delete sync;
}
