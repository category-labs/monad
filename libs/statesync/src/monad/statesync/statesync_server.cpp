#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/basic_formatter.hpp>
#include <monad/core/block.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/traverse.hpp>
#include <monad/statesync/statesync_server.h>
#include <monad/statesync/statesync_server_context.hpp>

#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <chrono>
#include <fcntl.h>
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
        monad_statesync_server_network *, unsigned char const *key,
        uint64_t key_size, unsigned char const *value, uint64_t value_size,
        bool code);
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
    monad_statesync_server_context const &ctx)
{
    MONAD_ASSERT(
        rq.old_target <= rq.target || rq.old_target == INVALID_BLOCK_ID);

    if (rq.old_target == INVALID_BLOCK_ID) {
        return true;
    }

    auto const &deleted = ctx.deleted;
    auto const prefix = from_prefix(rq.prefix, rq.prefix_bytes);

    for (uint64_t i = rq.old_target + 1; i <= rq.target; ++i) {
        Deleted::const_accessor it;
        if (!deleted.find(it, i)) {
            return false;
        }
        for (auto const &[key, storage] : it->second) {
            MONAD_ASSERT(key.size() == sizeof(bytes32_t));
            if (!key.starts_with(prefix)) {
                continue;
            }
            if (storage.empty()) {
                sync->statesync_server_send_upsert(
                    sync->net, key.data(), key.size(), nullptr, 0, false);
            }
            else {
                for (auto const &skey : storage) {
                    auto const dkey = key + skey;
                    sync->statesync_server_send_upsert(
                        sync->net, dkey.data(), dkey.size(), nullptr, 0, false);
                }
            }
        }
    }
    return true;
}

bool statesync_server_handle_request(
    monad_statesync_server *const sync, monad_sync_request const rq)
{
    struct Traverse final : public TraverseMachine
    {
        enum class Section : uint8_t
        {
            None,
            State,
            Code
        } section;
        monad_statesync_server *sync;
        NibblesView prefix;
        Nibbles path;
        uint64_t from;
        uint64_t until;

        Traverse(
            monad_statesync_server *const sync, NibblesView const prefix,
            uint64_t const from, uint64_t const until)
            : section{Section::None}
            , sync{sync}
            , prefix{prefix}
            , from{from}
            , until{until}
        {
        }

        virtual bool down(unsigned char const branch, Node const &node) override
        {
            if (section == Section::None) {
                MONAD_ASSERT(branch != RECEIPT_NIBBLE);
                if (branch == STATE_NIBBLE) {
                    section = Section::State;
                }
                else if (branch == CODE_NIBBLE) {
                    section = Section::Code;
                }
                return true;
            }

            if (path.nibble_size() < prefix.nibble_size()) {
                MONAD_ASSERT(prefix.get(path.nibble_size()) == branch);
                auto const ext = node.path_nibble_view();
                auto const rest = prefix.substr(path.nibble_size() + 1);
                for (unsigned i = 0;
                     i < ext.nibble_size() && i < rest.nibble_size();
                     ++i) {
                    if (ext.get(i) != rest.get(i)) {
                        return false;
                    }
                }
            }

            MONAD_ASSERT(node.version >= 0);
            auto const v = static_cast<uint64_t>(node.version);
            if (v < from) {
                return false;
            }

            path = concat(NibblesView{path}, branch, node.path_nibble_view());

            // TODO: change this to send the unhashed key, get rid of
            // NibblesView::data
            constexpr auto HASH_SIZE = KECCAK256_SIZE * 2;
            auto const n = path.nibble_size();
            if ((n == HASH_SIZE || n == HASH_SIZE * 2) && v <= until) {
                MONAD_ASSERT(n == HASH_SIZE || section == Section::State);
                MONAD_ASSERT(NibblesView{path}.starts_with(prefix));
                MONAD_ASSERT(node.has_value());
                sync->statesync_server_send_upsert(
                    sync->net,
                    path.data(),
                    path.nibble_size() / 2,
                    node.value().data(),
                    node.value().size(),
                    section == Section::Code);
            }

            return true;
        }

        virtual void up(unsigned char const branch, Node const &node) override
        {
            if (path.empty()) {
                section = Section::None;
                return;
            }
            auto const path_view = NibblesView{path};
            auto const rem_size = [&] {
                if (branch == INVALID_BRANCH) {
                    return 0;
                }
                int const rem_size = path_view.nibble_size() - 1 -
                                     node.path_nibble_view().nibble_size();
                MONAD_ASSERT(rem_size >= 0);
                MONAD_ASSERT(
                    path_view.substr(static_cast<unsigned>(rem_size)) ==
                    concat(branch, node.path_nibble_view()));
                return rem_size;
            }();
            path = path_view.substr(0, static_cast<unsigned>(rem_size));
        }

        virtual std::unique_ptr<TraverseMachine> clone() const override
        {
            return std::make_unique<Traverse>(*this);
        }

        virtual bool
        should_visit(Node const &node, unsigned char const branch) override
        {
            if (section == Section::None) {
                return branch == STATE_NIBBLE || branch == CODE_NIBBLE;
            }
            auto const v =
                node.subtrie_min_version(node.to_child_index(branch));
            MONAD_ASSERT(v >= 0);
            if (static_cast<uint64_t>(v) > until) {
                return false;
            }
            return path.nibble_size() >= prefix.nibble_size() ||
                   prefix.get(path.nibble_size()) == branch;
        }
    };

    auto const start = std::chrono::steady_clock::now();
    auto *const ctx = sync->context;
    if (!send_deletion(sync, rq, *ctx)) {
        LOG_INFO("failed when sending deletions");
        return false;
    }
    auto &db = *ctx->ro;

    auto const bytes = from_prefix(rq.prefix, rq.prefix_bytes);
    auto const root = db.load_root_for_version(rq.target);
    if (!root.is_valid()) {
        return false;
    }
    auto const begin = std::chrono::steady_clock::now();
    Traverse traverse(sync, NibblesView{bytes}, rq.from, rq.until);
    if (!db.traverse(root, traverse, rq.target)) {
        LOG_INFO("failed when handling the traverse");
        return false;
    }
    auto const end = std::chrono::steady_clock::now();

    LOG_DEBUG(
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
            "target={}",
            rq.prefix,
            rq.from,
            rq.until,
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
        monad_statesync_server_network *, unsigned char const *key,
        uint64_t key_size, unsigned char const *value, uint64_t value_size,
        bool code),
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
    MONAD_ASSERT(buf[0] == SyncTypeRequest);
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
