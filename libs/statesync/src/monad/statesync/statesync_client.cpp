#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/db/trie_db.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_protocol.hpp>
#include <monad/statesync/statesync_version.h>

#include <algorithm>
#include <filesystem>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context *monad_statesync_client_context_create(
    char const *const *const dbname_paths, size_t const len,
    char const *const genesis_file, monad_statesync_client *sync,
    void (*statesync_send_request)(
        monad_statesync_client *, monad_sync_request))
{
    std::vector<std::filesystem::path> const paths{
        dbname_paths, dbname_paths + len};
    MONAD_ASSERT(!paths.empty());
    return new monad_statesync_client_context{
        paths, genesis_file, sync, statesync_send_request};
}

uint8_t monad_statesync_client_prefix_bytes()
{
    return 1;
}

size_t monad_statesync_client_prefixes()
{
    return 1 << (8 * monad_statesync_client_prefix_bytes());
}

bool monad_statesync_client_has_reached_target(
    monad_statesync_client_context const *const ctx)
{
    if (ctx->target == INVALID_BLOCK_ID) {
        return false;
    }

    for (auto const &[n, _] : ctx->progress) {
        MONAD_ASSERT(n == INVALID_BLOCK_ID || n <= ctx->target);
        if (n != ctx->target) {
            return false;
        }
    }
    return true;
}

void monad_statesync_client_handle_new_peer(
    monad_statesync_client_context *const ctx, uint64_t const prefix,
    uint32_t const version)
{
    MONAD_ASSERT(monad_statesync_client_compatible(version));
    auto &ptr = ctx->protocol.at(prefix);
    // TODO: handle switching peers
    MONAD_ASSERT(!ptr);
    switch (version) {
    case 1:
        ptr = std::make_unique<StatesyncProtocolV1>();
        break;
    default:
        MONAD_ASSERT(false);
    };
}

void monad_statesync_client_handle_target(
    monad_statesync_client_context *const ctx, monad_sync_target const msg)
{
    MONAD_ASSERT(std::ranges::all_of(
        ctx->protocol, [](auto const &ptr) { return ptr != nullptr; }))
    MONAD_ASSERT(msg.n != INVALID_BLOCK_ID);
    MONAD_ASSERT(ctx->target == INVALID_BLOCK_ID || msg.n >= ctx->target);

    ctx->target = msg.n;
    ctx->expected_root =
        to_bytes(byte_string_view{msg.state_root, sizeof(bytes32_t)});

    if (msg.n == ctx->db.get_latest_block_id()) {
        MONAD_ASSERT(monad_statesync_client_has_reached_target(ctx));
    }
    else if (msg.n == 0) {
        MONAD_ASSERT(ctx->db.get_latest_block_id() == INVALID_BLOCK_ID);
        read_genesis(ctx->genesis, ctx->tdb);
        ctx->progress.assign(ctx->progress.size(), {msg.n, INVALID_BLOCK_ID});
    }
    else {
        for (size_t i = 0; i < ctx->progress.size(); ++i) {
            ctx->protocol.at(i)->send_request(ctx, i);
        }
    }
}

bool monad_statesync_client_handle_upsert(
    monad_statesync_client_context *const ctx, uint64_t const prefix,
    monad_sync_type const type, unsigned char const *const val,
    uint64_t const size)
{
    return ctx->protocol.at(prefix)->handle_upsert(ctx, type, val, size);
}

void monad_statesync_client_handle_done(
    monad_statesync_client_context *const ctx, monad_sync_done const msg)
{
    MONAD_ASSERT(msg.success);

    auto &[progress, old_target] = ctx->progress.at(msg.prefix);
    MONAD_ASSERT(msg.n > progress || progress == INVALID_BLOCK_ID);
    progress = msg.n;
    old_target = ctx->target;

    if (progress != ctx->target) {
        ctx->protocol.at(msg.prefix)->send_request(ctx, msg.prefix);
    }

    if (MONAD_UNLIKELY(monad_statesync_client_has_reached_target(ctx))) {
        ctx->commit();
    }
}

bool monad_statesync_client_finalize(monad_statesync_client_context *const ctx)
{
    MONAD_ASSERT(ctx->deltas.empty());
    if (!ctx->buffered.empty()) {
        // sent storage with no account
        return false;
    }

    if (ctx->db.get_latest_block_id() != ctx->target) {
        ctx->db.move_trie_version_forward(
            ctx->db.get_latest_block_id(), ctx->target);
    }
    TrieDb db{ctx->db};
    MONAD_ASSERT(db.get_block_number() == ctx->target);

    for (auto const &hash : ctx->hash) {
        if (db.read_code(hash) == nullptr) {
            return false;
        }
    }
    return db.state_root() == ctx->expected_root;
}

void monad_statesync_client_context_destroy(
    monad_statesync_client_context *const ctx)
{
    delete ctx;
}
