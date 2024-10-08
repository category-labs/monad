#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/likely.h>
#include <monad/core/rlp/bytes_rlp.hpp>
#include <monad/core/unaligned.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>

#include <ankerl/unordered_dense.h>

#include <bit>
#include <deque>
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
    std::deque<mpt::Update> alloc;
    std::deque<byte_string> bytes_alloc;
    std::deque<hash256> hash_alloc;
    UpdateList accounts;
    for (auto const &[addr, delta] : ctx.deltas) {
        UpdateList storage;
        std::optional<byte_string_view> value;
        if (delta.has_value()) {
            auto const &[acct, deltas] = delta.value();
            value = bytes_alloc.emplace_back(encode_account_db(addr, acct));
            for (auto const &[key, val] : deltas) {
                storage.push_front(alloc.emplace_back(Update{
                    .key = hash_alloc.emplace_back(keccak256(key.bytes)),
                    .value = val == bytes32_t{}
                                 ? std::nullopt
                                 : std::make_optional<byte_string_view>(
                                       bytes_alloc.emplace_back(
                                           encode_storage_db(key, val))),
                    .incarnation = false,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(ctx.current)}));
            }
        }
        accounts.push_front(alloc.emplace_back(Update{
            .key = hash_alloc.emplace_back(keccak256(addr.bytes)),
            .value = value,
            .incarnation = false,
            .next = std::move(storage),
            .version = static_cast<int64_t>(ctx.current)}));
    }
    UpdateList code_updates;

    ankerl::unordered_dense::segmented_set<bytes32_t> remaining;
    std::deque<bytes32_t> upserted;
    for (auto const &hash : ctx.hash) {
        if (ctx.code.contains(hash)) {
            code_updates.push_front(alloc.emplace_back(Update{
                .key = NibblesView{hash},
                .value = ctx.code.at(hash),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(ctx.current)}));
            upserted.emplace_back(hash);
        }
        else {
            remaining.insert(hash);
        }
    }

    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(accounts),
        .version = static_cast<int64_t>(ctx.current)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(ctx.current)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    ctx.db.upsert(std::move(updates), ctx.current, false, false);
    ctx.tdb.set_block_number(ctx.current);
    for (auto const &hash : upserted) {
        MONAD_ASSERT(ctx.code.erase(hash) == 1);
    }
    ctx.hash = std::move(remaining);
    ctx.deltas.clear();
}

void account_update(
    monad_statesync_client_context &ctx, Address const &addr,
    std::optional<Account> const &acct)
{
    using StorageDeltas = monad_statesync_client_context::StorageDeltas;

    if (acct.has_value() && acct.value().code_hash != NULL_HASH) {
        ctx.hash.insert(acct.value().code_hash);
    }

    auto const it = ctx.deltas.find(addr);
    auto const updated = it != ctx.deltas.end();

    if (ctx.buffered.contains(addr)) {
        MONAD_ASSERT(!ctx.tdb.read_account(addr).has_value() && !updated);
        if (acct.has_value()) {
            MONAD_ASSERT(
                ctx.deltas
                    .emplace(
                        addr,
                        std::make_pair(
                            acct.value(), std::move(ctx.buffered.at(addr))))
                    .second);
        }
        ctx.buffered.erase(addr);
    }
    else if (!updated) {
        if (acct.has_value()) {
            MONAD_ASSERT(
                ctx.deltas
                    .emplace(
                        addr, std::make_pair(acct.value(), StorageDeltas{}))
                    .second);
        }
        else if (ctx.tdb.read_account(addr).has_value()) {
            MONAD_ASSERT(ctx.deltas.emplace(addr, std::nullopt).second);
        }
    }
    // incarnation
    else if (acct.has_value() && !it->second.has_value()) {
        commit(ctx);
        account_update(ctx, addr, acct);
    }
    else if (acct.has_value()) {
        std::get<Account>(it->second.value()) = acct.value();
    }
    else if (ctx.tdb.read_account(addr).has_value()) {
        it->second = std::nullopt;
    }
    else {
        ctx.deltas.erase(it);
    }
}

void storage_update(
    monad_statesync_client_context &ctx, Address const &addr,
    bytes32_t const &key, bytes32_t const &val)
{
    using StorageDeltas = monad_statesync_client_context::StorageDeltas;

    auto const it = ctx.deltas.find(addr);
    auto const updated = it != ctx.deltas.end();

    if (ctx.buffered.contains(addr)) {
        MONAD_ASSERT(!ctx.tdb.read_account(addr).has_value() && !updated);
        if (val == bytes32_t{}) {
            ctx.buffered[addr].erase(key);
            if (ctx.buffered[addr].empty()) {
                ctx.buffered.erase(addr);
            }
        }
        else {
            auto const sit = ctx.buffered[addr].find(key);
            if (sit != ctx.buffered[addr].end()) {
                sit->second = val;
            }
            else {
                MONAD_ASSERT(ctx.buffered[addr].emplace(key, val).second);
            }
        }
    }
    else if (
        val != bytes32_t{} || read_storage(ctx, addr, key) != bytes32_t{}) {
        if (updated) {
            if (it->second.has_value()) {
                std::get<StorageDeltas>(it->second.value())[key] = val;
            }
            // incarnation
            else if (val != bytes32_t{}) {
                commit(ctx);
                storage_update(ctx, addr, key, val);
            }
        }
        else {
            auto const orig = ctx.tdb.read_account(addr);
            if (orig.has_value()) {
                MONAD_ASSERT(
                    ctx.deltas
                        .emplace(
                            addr,
                            std::make_pair(
                                orig.value(), StorageDeltas{{key, val}}))
                        .second);
            }
            else {
                MONAD_ASSERT(val != bytes32_t{});
                MONAD_ASSERT(
                    ctx.buffered.emplace(addr, StorageDeltas{{key, val}})
                        .second);
            }
        }
    }
    else if (updated && it->second.has_value()) {
        MONAD_ASSERT(val == bytes32_t{});
        std::get<StorageDeltas>(it->second.value()).erase(key);
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

    for (auto const &[n, _] : ctx->progress) {
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
        ctx->progress.assign(ctx->progress.size(), {msg.n, INVALID_BLOCK_ID});
    }
    else {
        for (size_t i = 0; i < ctx->progress.size(); ++i) {
            auto const &[progress, old_target] = ctx->progress[i];
            MONAD_ASSERT(progress == INVALID_BLOCK_ID || progress < msg.n);
            auto const from = progress == INVALID_BLOCK_ID ? 0 : progress + 1;
            ctx->statesync_send_request(
                ctx->sync,
                monad_sync_request{
                    .prefix = i,
                    .prefix_bytes = ctx->prefix_bytes,
                    .target = msg.n,
                    .from = from,
                    .until =
                        from >= (msg.n * 99 / 100) ? msg.n : msg.n * 99 / 100,
                    .old_target = old_target});
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

    auto &[progress, old_target] = ctx->progress.at(msg.prefix);
    MONAD_ASSERT(msg.n > progress || progress == INVALID_BLOCK_ID);
    progress = msg.n;
    old_target = ctx->target;

    if (progress != ctx->target) {
        ctx->statesync_send_request(
            ctx->sync,
            monad_sync_request{
                .prefix = msg.prefix,
                .prefix_bytes = ctx->prefix_bytes,
                .target = ctx->target,
                .from = progress + 1,
                .until = std::min(progress + (1 << 20), ctx->target),
                .old_target = ctx->target});
    }

    if (MONAD_UNLIKELY(monad_statesync_client_has_reached_target(ctx))) {
        commit(*ctx);
    }
}

bool monad_statesync_client_finalize(monad_statesync_client_context *const ctx)
{
    MONAD_ASSERT(ctx->deltas.empty());
    if (!ctx->buffered.empty() || !ctx->hash.empty()) {
        // sent storage with no account or not all code was sent
        return false;
    }

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
