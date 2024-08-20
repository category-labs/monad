#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>

#include <bit>
#include <filesystem>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bytes32_t read_storage(
    monad_statesync_client_context &ctx, Address const &addr,
    bytes32_t const &key)
{
    return ctx.tdb.read_storage(addr, Incarnation{0, 0}, key);
}

void commit(monad_statesync_client_context &ctx)
{
    Code code;
    std::unordered_set<bytes32_t> remaining;
    for (auto const &hash : ctx.hash) {
        auto const it = ctx.code.find(hash);
        if (it != ctx.code.end()) {
            MONAD_ASSERT(code.emplace(
                hash, std::make_shared<CodeAnalysis>(analyze(it->second))));
            ctx.code.erase(it);
        }
        else {
            remaining.insert(hash);
        }
    }
    ctx.hash = std::move(remaining);

    ctx.tdb.set_block_number(ctx.current);
    ctx.tdb.commit(ctx.deltas, code);
    ctx.deltas.clear();
}

void account_update(
    monad_statesync_client_context &ctx, Address const &addr,
    std::optional<Account> const &acct)
{
    if (acct.has_value() && acct.value().code_hash != NULL_HASH) {
        ctx.hash.insert(acct.value().code_hash);
    }

    StateDeltas::accessor it;
    auto const updated = ctx.deltas.find(it, addr);

    if (ctx.buffered.contains(addr)) {
        MONAD_ASSERT(!ctx.tdb.read_account(addr).has_value() && !updated);
        if (acct.has_value()) {
            MONAD_ASSERT(ctx.deltas.emplace(
                addr,
                StateDelta{
                    .account = {std::nullopt, acct},
                    .storage = std::move(ctx.buffered.at(addr))}));
        }
        ctx.buffered.erase(addr);
    }
    else if (!updated) {
        MONAD_ASSERT(ctx.deltas.emplace(
            it,
            addr,
            StateDelta{
                .account = {ctx.tdb.read_account(addr), acct}, .storage = {}}));
    }
    else if ( // incarnation
        it->second.account.first.has_value() &&
        !it->second.account.second.has_value() && acct.has_value()) {
        it.release();
        commit(ctx);
        account_update(ctx, addr, acct);
    }
    else {
        it->second.account.second = acct;
    }
}

void storage_update(
    monad_statesync_client_context &ctx, Address const &addr,
    bytes32_t const &key, bytes32_t const &val)
{
    StateDeltas::accessor it;
    auto const updated = ctx.deltas.find(it, addr);

    if (ctx.buffered.contains(addr)) {
        MONAD_ASSERT(!ctx.tdb.read_account(addr).has_value() && !updated);
        if (val == bytes32_t{}) {
            ctx.buffered[addr].erase(key);
            if (ctx.buffered[addr].empty()) {
                ctx.buffered.erase(addr);
            }
        }
        else {
            StorageDeltas::accessor sit;
            if (ctx.buffered[addr].find(sit, key)) {
                sit->second.second = val;
            }
            else {
                MONAD_ASSERT(
                    ctx.buffered[addr].emplace(key, StorageDelta{{}, val}));
            }
        }
    }
    else if (updated) {
        StorageDeltas::accessor sit;
        if (it->second.storage.find(sit, key)) {
            sit->second.second = val;
        }
        else {
            MONAD_ASSERT(it->second.storage.emplace(
                key, StorageDelta{read_storage(ctx, addr, key), val}));
        }
    }
    else {
        auto const orig = ctx.tdb.read_account(addr);
        if (!orig.has_value()) {
            MONAD_ASSERT(
                ctx.buffered[addr].emplace(key, StorageDelta{{}, val}));
        }
        else {
            MONAD_ASSERT(ctx.deltas.emplace(
                addr,
                StateDelta{
                    .account = {orig, orig},
                    .storage = {{key, {read_storage(ctx, addr, key), val}}}}));
        }
    }
}

MONAD_ANONYMOUS_NAMESPACE_END

monad_statesync_client_context *monad_statesync_client_context_create(
    char const *const *const dbname_paths, size_t const len,
    char const *const genesis_file, monad_statesync_client *sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request))
{
    std::vector<std::filesystem::path> const paths{
        dbname_paths, dbname_paths + len};
    MONAD_ASSERT(!paths.empty());
    return new monad_statesync_client_context{
        paths, genesis_file, 1, sync, statesync_send_request};
}

bool monad_statesync_client_has_reached_target(
    monad_statesync_client_context const *const ctx)
{
    if (ctx->target == INVALID_BLOCK_ID) {
        return false;
    }

    for (auto const &n : ctx->progress) {
        MONAD_ASSERT(n == INVALID_BLOCK_ID || n <= ctx->target);
        if (n != ctx->target) {
            return false;
        }
    }
    return true;
}

void monad_statesync_client_handle_target(
    monad_statesync_client_context *const ctx, monad_sync_target const msg)
{
    MONAD_ASSERT(msg.n != INVALID_BLOCK_ID);
    MONAD_ASSERT(ctx->target == INVALID_BLOCK_ID || msg.n >= ctx->target);

    if (msg.n == ctx->db.get_latest_block_id()) {
        MONAD_ASSERT(monad_statesync_client_has_reached_target(ctx));
    }
    else if (msg.n == 0) {
        MONAD_ASSERT(ctx->db.get_latest_block_id() == INVALID_BLOCK_ID);
        read_genesis(ctx->genesis, ctx->tdb);
        ctx->progress.assign(ctx->progress.size(), msg.n);
    }
    else {
        auto const &progress = ctx->progress;
        for (size_t i = 0; i < progress.size(); ++i) {
            MONAD_ASSERT(
                progress[i] == INVALID_BLOCK_ID || progress[i] < msg.n);
            auto const from =
                progress[i] == INVALID_BLOCK_ID ? 0 : progress[i] + 1;
            ctx->statesync_send_request(
                ctx->sync,
                monad_sync_request{
                    .prefix = i,
                    .prefix_bytes = ctx->prefix_bytes,
                    .target = msg.n,
                    .from = from,
                    .until =
                        from >= (msg.n * 99 / 100) ? msg.n : msg.n * 99 / 100,
                    .old_target = ctx->target});
        }
    }
    ctx->target = msg.n;
    ctx->expected_root =
        to_bytes(byte_string_view{msg.state_root, sizeof(bytes32_t)});
}

void monad_statesync_client_handle_upsert(
    monad_statesync_client_context *const ctx, monad_sync_type const type,
    unsigned char const *const val, uint64_t const size)
{
    byte_string_view raw{val, size};
    if (type == SyncTypeUpsertCode) {
        // code is immutable once inserted - no deletions
        ctx->code.emplace(std::bit_cast<bytes32_t>(keccak256(raw)), raw);
    }
    else if (type == SyncTypeUpsertAccount) {
        auto const res = decode_account_db(raw);
        MONAD_ASSERT(res.has_value());
        auto [addr, acct] = res.value();
        acct.incarnation = Incarnation{0, 0};
        account_update(*ctx, addr, acct);
    }
    else if (type == SyncTypeUpsertStorage) {
        MONAD_ASSERT(size >= sizeof(Address));
        raw.remove_prefix(sizeof(Address));
        auto const res = decode_storage_db(raw);
        MONAD_ASSERT(res.has_value());
        auto const &[k, v] = res.value();
        storage_update(*ctx, unaligned_load<Address>(val), k, v);
    }
    else if (type == SyncTypeUpsertAccountDelete) {
        MONAD_ASSERT(size == sizeof(Address));
        account_update(*ctx, unaligned_load<Address>(val), std::nullopt);
    }
    else {
        MONAD_ASSERT(type == SyncTypeUpsertStorageDelete);
        MONAD_ASSERT(size >= sizeof(Address));
        raw.remove_prefix(sizeof(Address));
        auto const res = rlp::decode_bytes32_compact(raw);
        MONAD_ASSERT(res.has_value());
        storage_update(*ctx, unaligned_load<Address>(val), res.value(), {});
    }

    if ((++ctx->n_upserts % (1 << 20)) == 0) {
        commit(*ctx);
    }
}

void monad_statesync_client_handle_done(
    monad_statesync_client_context *const ctx, monad_sync_done const msg)
{
    MONAD_ASSERT(msg.success);

    auto &p = ctx->progress.at(msg.prefix);
    MONAD_ASSERT(msg.n > p || p == INVALID_BLOCK_ID);
    p = msg.n;

    if (p != ctx->target) {
        ctx->statesync_send_request(
            ctx->sync,
            monad_sync_request{
                .prefix = msg.prefix,
                .prefix_bytes = ctx->prefix_bytes,
                .target = ctx->target,
                .from = p + 1,
                .until = std::min(p + (1 << 20), ctx->target),
                .old_target = ctx->target});
    }

    if (MONAD_UNLIKELY(monad_statesync_client_has_reached_target(ctx))) {
        commit(*ctx);
    }
}

bool monad_statesync_client_finalize(monad_statesync_client_context *const ctx)
{
    MONAD_ASSERT(
        ctx->buffered.empty() && ctx->deltas.empty() && ctx->hash.empty());
    if (ctx->db.get_latest_block_id() != ctx->target) {
        ctx->db.move_trie_version_forward(
            ctx->db.get_latest_block_id(), ctx->target);
    }
    TrieDb db{ctx->db};
    MONAD_ASSERT(db.get_block_number() == ctx->target);
    return db.state_root() == ctx->expected_root;
}

void monad_statesync_client_context_destroy(
    monad_statesync_client_context *const ctx)
{
    delete ctx;
}
