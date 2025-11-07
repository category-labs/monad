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

#include <category/async/io.hpp>
#include <category/core/assert.h>
#include <category/core/basic_formatter.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/traverse.hpp>
#include <category/statesync/statesync_server.h>
#include <category/statesync/statesync_server_context.hpp>

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

// validate the request sent by client
bool static_validate_request(monad_sync_request const &rq)
{
    // sanity check the number of bytes in the prefix
    constexpr size_t MAX_PREFIX_BYTES = sizeof(decltype(rq.prefix));
    static_assert(MAX_PREFIX_BYTES == 8);
    if (rq.prefix_bytes > MAX_PREFIX_BYTES) {
        LOG_INFO(
            "Invalid request: prefix_bytes={} exceeds maximum={}",
            rq.prefix_bytes,
            MAX_PREFIX_BYTES);
        return false;
    }

    // validate target
    if (rq.target == INVALID_BLOCK_NUM) {
        LOG_INFO(
            "Invalid request: target cannot be INVALID_BLOCK_NUM ({})",
            INVALID_BLOCK_NUM);
        return false;
    }

    // Validate block number ordering: from <= until <= target
    if (rq.from > rq.until) {
        LOG_INFO("Invalid request: from={} > until={}", rq.from, rq.until);
        return false;
    }

    if (rq.until > rq.target) {
        LOG_INFO("Invalid request: until={} > target={}", rq.until, rq.target);
        return false;
    }

    // Validate old_target == INVALID_BLOCK_NUM || old_target <= target
    if (rq.old_target != INVALID_BLOCK_NUM) {
        if (rq.old_target > rq.target) {
            LOG_INFO(
                "Invalid request: old_target={} > target={}",
                rq.old_target,
                rq.target);
            return false;
        }
    }

    return true;
}

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
    monad_statesync_server_context &ctx, uint64_t *const num_upserts,
    uint64_t *const upsert_bytes)
{
    MONAD_ASSERT(
        rq.old_target <= rq.target || rq.old_target == INVALID_BLOCK_NUM);

    if (rq.old_target == INVALID_BLOCK_NUM) {
        return true;
    }

    auto const fn = [sync,
                     prefix = from_prefix(rq.prefix, rq.prefix_bytes),
                     num_upserts,
                     upsert_bytes](Deletion const &deletion) {
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
            ++(*num_upserts);
            *upsert_bytes += sizeof(addr);
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
            ++(*num_upserts);
            *upsert_bytes += sizeof(addr) + skey.size();
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
    uint64_t disk_ios_start = 0;
    uint64_t disk_bytes_start = 0;
    auto const *io = monad::async::AsyncIO::thread_instance();
    if (io != nullptr) {
        disk_ios_start = io->total_reads_submitted();
        disk_bytes_start = io->total_bytes_read();
    }

    uint64_t num_upserts = 0;
    uint64_t upsert_bytes = 0;

    struct Traverse final : public TraverseMachine
    {
        unsigned char nibble;
        unsigned depth;
        Address addr;
        monad_statesync_server *sync;
        NibblesView prefix;
        uint64_t from;
        uint64_t until;
        uint64_t *num_upserts;
        uint64_t *upsert_bytes;

        Traverse(
            monad_statesync_server *const sync, NibblesView const prefix,
            uint64_t const from, uint64_t const until,
            uint64_t *const num_upserts, uint64_t *const upsert_bytes)
            : nibble{INVALID_BRANCH}
            , depth{0}
            , sync{sync}
            , prefix{prefix}
            , from{from}
            , until{until}
            , num_upserts{num_upserts}
            , upsert_bytes{upsert_bytes}
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (branch == INVALID_BRANCH) {
                MONAD_ASSERT(depth == 0);
                return true;
            }
            else if (depth == 0 && nibble == INVALID_BRANCH) {
                nibble = branch;
                return true;
            }

            MONAD_ASSERT(nibble == STATE_NIBBLE || nibble == CODE_NIBBLE);
            MONAD_ASSERT(
                depth >= prefix.nibble_size() || prefix.get(depth) == branch);
            auto const ext = node.path_nibble_view();
            for (auto i = depth + 1; i < prefix.nibble_size(); ++i) {
                auto const j = i - (depth + 1);
                if (j >= ext.nibble_size()) {
                    break;
                }
                if (ext.get(j) != prefix.get(i)) {
                    return false;
                }
            }

            MONAD_ASSERT(node.version >= 0);
            auto const v = static_cast<uint64_t>(node.version);
            if (v < from) {
                return false;
            }

            depth += 1 + ext.nibble_size();

            constexpr unsigned HASH_SIZE = KECCAK256_SIZE * 2;
            bool const account = depth == HASH_SIZE && nibble == STATE_NIBBLE;
            if (account && node.number_of_children() > 0) {
                MONAD_ASSERT(node.has_value());
                auto raw = node.value();
                auto const res = decode_account_db(raw);
                MONAD_ASSERT(res.has_value());
                addr = std::get<Address>(res.assume_value());
            }

            if (node.has_value() && v <= until) {
                auto const send_upsert = [&](monad_sync_type const type,
                                             unsigned char const *const v1 =
                                                 nullptr,
                                             uint64_t const size1 = 0) {
                    uint64_t const size2 = node.value().size();
                    sync->statesync_server_send_upsert(
                        sync->net, type, v1, size1, node.value().data(), size2);
                    ++(*num_upserts);
                    *upsert_bytes += size1 + size2;
                };

                if (nibble == CODE_NIBBLE) {
                    MONAD_ASSERT(depth == HASH_SIZE);
                    send_upsert(SYNC_TYPE_UPSERT_CODE);
                }
                else {
                    MONAD_ASSERT(nibble == STATE_NIBBLE);
                    if (depth == HASH_SIZE) {
                        send_upsert(SYNC_TYPE_UPSERT_ACCOUNT);
                    }
                    else {
                        MONAD_ASSERT(depth == (HASH_SIZE * 2));
                        send_upsert(
                            SYNC_TYPE_UPSERT_STORAGE,
                            reinterpret_cast<unsigned char *>(&addr),
                            sizeof(addr));
                    }
                }
            }

            return true;
        }

        virtual void up(unsigned char const, Node const &node) override
        {
            if (depth == 0) {
                nibble = INVALID_BRANCH;
                return;
            }
            unsigned const subtrahend = 1 + node.path_nibbles_len();
            MONAD_ASSERT(depth >= subtrahend);
            depth -= subtrahend;
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }

        virtual bool
        should_visit(Node const &node, unsigned char const branch) override
        {
            if (depth == 0 && nibble == INVALID_BRANCH) {
                MONAD_ASSERT(branch != INVALID_BRANCH);
                return branch == STATE_NIBBLE || branch == CODE_NIBBLE;
            }
            auto const v =
                node.subtrie_min_version(node.to_child_index(branch));
            MONAD_ASSERT(v >= 0);
            if (static_cast<uint64_t>(v) > until) {
                return false;
            }
            return depth >= prefix.nibble_size() || prefix.get(depth) == branch;
        }
    };

    if (MONAD_UNLIKELY(!static_validate_request(rq))) {
        return false;
    }

    // load the target root to verify existence of target
    auto *const ctx = sync->context;
    auto &db = *ctx->ro;
    NodeCursor const root{db.load_root_for_version(rq.target)};
    if (!root.is_valid()) {
        return false;
    }

    [[maybe_unused]] auto const start = std::chrono::steady_clock::now();
    if (rq.prefix < 256 && rq.target > rq.prefix) {
        auto const version = rq.target - rq.prefix - 1;
        NodeCursor const root{db.load_root_for_version(version)};
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
        ++num_upserts;
        upsert_bytes += val.size();
    }

    if (!send_deletion(sync, rq, *ctx, &num_upserts, &upsert_bytes)) {
        return false;
    }

    auto const bytes = from_prefix(rq.prefix, rq.prefix_bytes);
    auto const finalized_root_res = db.find(root, finalized_nibbles, rq.target);
    if (!finalized_root_res.has_value()) {
        return false;
    }
    auto const &finalized_root = finalized_root_res.value();
    if (db.find(finalized_root, state_nibbles, rq.target).has_error() ||
        db.find(finalized_root, code_nibbles, rq.target).has_error()) {
        return false;
    }

    [[maybe_unused]] auto const begin = std::chrono::steady_clock::now();
    Traverse traverse(
        sync,
        NibblesView{bytes},
        rq.from,
        rq.until,
        &num_upserts,
        &upsert_bytes);
    if (!db.traverse(finalized_root, traverse, rq.target)) {
        return false;
    }
    [[maybe_unused]] auto const end = std::chrono::steady_clock::now();

    uint64_t disk_ios_submitted = 0;
    uint64_t disk_bytes_total = 0;
    if (io != nullptr) {
        disk_ios_submitted = io->total_reads_submitted() - disk_ios_start;
        disk_bytes_total = io->total_bytes_read() - disk_bytes_start;
    }

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

    auto const elapsed_seconds =
        std::chrono::duration_cast<std::chrono::duration<double>>(end - start)
            .count();
    [[maybe_unused]] double disk_ios_per_sec = 0.0;
    [[maybe_unused]] double disk_bytes_per_sec = 0.0;
    [[maybe_unused]] double upsert_bytes_per_sec = 0.0;
    if (elapsed_seconds > 0.0) {
        disk_ios_per_sec =
            static_cast<double>(disk_ios_submitted) / elapsed_seconds;
        disk_bytes_per_sec =
            static_cast<double>(disk_bytes_total) / elapsed_seconds;
        upsert_bytes_per_sec =
            static_cast<double>(upsert_bytes) / elapsed_seconds;
    }

    LOG_INFO(
        "session metrics: disk_ios={} disk_bytes={} num_upserts={} "
        "upsert_bytes={} | disk_ios/s={:.1f} disk_bytes/s={:.1f} "
        "upsert_bytes/s={:.1f}",
        disk_ios_submitted,
        disk_bytes_total,
        num_upserts,
        upsert_bytes,
        disk_ios_per_sec,
        disk_bytes_per_sec,
        upsert_bytes_per_sec);

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
