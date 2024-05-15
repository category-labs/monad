#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/likely.h>
#include <monad/db/trie_db.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>

#include <bit>
#include <filesystem>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

constexpr Nibbles state_key(byte_string_view const key)
{
    return concat(STATE_NIBBLE, NibblesView{key});
}

void account_delete(SyncState &state, mpt::Db &db, byte_string_view const key)
{
    auto const val = db.get(state_key(key), db.get_latest_block_id());
    if (val.has_value()) {
        MONAD_ASSERT(!val.assume_value().empty())
        state[key] = {.value = {}, .incarnation = false, .storage = {}};
    }
    else if (auto it = state.find(key); it != state.end()) {
        state.erase(it);
    }
}

void storage_delete(SyncState &state, mpt::Db &db, byte_string_view const key)
{
    auto const akey = key.substr(0, sizeof(bytes32_t));
    auto const skey = key.substr(sizeof(bytes32_t), sizeof(bytes32_t));
    auto const val = db.get(state_key(key), db.get_latest_block_id());
    if (val.has_value()) {
        auto const acct = db.get(state_key(akey), db.get_latest_block_id());
        MONAD_ASSERT(acct.has_value() && !val.assume_value().empty())
        auto it = state
                      .emplace(
                          akey,
                          SyncEntry{
                              .value = byte_string{acct.assume_value()},
                              .incarnation = false,
                              .storage = {}})
                      .first;
        it->second.storage[skey] = {};
    }
    else if (state.contains(akey) && state[akey].storage.contains(skey)) {
        state[akey].storage.erase(skey);
        auto const acct = db.get(state_key(akey), db.get_latest_block_id());
        if (state[akey].storage.empty() && state[akey].value.empty() &&
            !acct.has_value()) {
            state.erase(akey);
        }
    }
}

void account_update(
    SyncState &state, std::unordered_set<bytes32_t> &hash,
    byte_string_view const key, byte_string_view const val)
{
    byte_string_view enc = val;
    auto after = decode_account_db(enc);
    MONAD_ASSERT(after.has_value());
    after.value().incarnation = Incarnation{0, 0};
    hash.insert(after.value().code_hash);
    auto it = state.find(key);
    if (it != state.end() && it->second.value.empty()) {
        it->second.incarnation = true;
    }
    it = state
             .emplace(
                 key,
                 SyncEntry{.value = {}, .incarnation = false, .storage = {}})
             .first;
    it->second.value = encode_account_db(after.value());
}

void storage_update(
    SyncState &state, mpt::Db &db, byte_string_view const key,
    byte_string_view val)
{
    MONAD_ASSERT(!val.empty());
    auto const akey = key.substr(0, sizeof(bytes32_t));
    auto const skey = key.substr(sizeof(bytes32_t), sizeof(bytes32_t));
    auto it = state.find(akey);
    if (it == state.end()) {
        auto const acct = db.get(state_key(akey), db.get_latest_block_id());
        it = state
                 .emplace(
                     akey,
                     SyncEntry{
                         .value = acct.has_value()
                                      ? byte_string{acct.assume_value()}
                                      : byte_string{},
                         .incarnation = false,
                         .storage = {}})
                 .first;
    }

    auto const res = decode_storage_db(val);
    MONAD_ASSERT(res.has_value());
    auto const to = encode_storage_db({}, res.value().second);
    it->second.storage[skey] = to;
}

void commit(monad_statesync_client_context &ctx, mpt::Db &db)
{
    std::list<mpt::Update> alloc;
    UpdateList accounts;
    SyncState tmp_state;
    for (auto &[key, entry] : ctx.state) {
        if (entry.value.empty() && !entry.storage.empty()) {
            tmp_state.emplace(key, std::move(entry));
            continue;
        }
        UpdateList storage;
        for (auto const &[skey, val] : entry.storage) {
            storage.push_front(alloc.emplace_back(Update{
                .key = NibblesView{skey},
                .value = val.empty()
                             ? std::nullopt
                             : std::make_optional<byte_string_view>(val),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(ctx.current)}));
        }
        accounts.push_front(alloc.emplace_back(Update{
            .key = NibblesView{key},
            .value = entry.value.empty()
                         ? std::nullopt
                         : std::make_optional<byte_string_view>(entry.value),
            .incarnation = entry.incarnation,
            .next = std::move(storage),
            .version = static_cast<int64_t>(ctx.current)}));
    }
    UpdateList code_updates;

    SyncCode tmp_code;
    for (auto &[key, val] : ctx.code) {
        if (ctx.hash.contains(key)) {
            code_updates.push_front(alloc.emplace_back(Update{
                .key = NibblesView{key},
                .value = val,
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(ctx.current)}));
        }
        else {
            tmp_code.emplace(key, std::move(val));
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
    db.upsert(std::move(updates), ctx.current);
    ctx.state = std::move(tmp_state);
    ctx.code = std::move(tmp_code);
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
        TrieDb db{ctx->db};
        read_genesis(ctx->genesis, db);
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
    std::memcpy(ctx->expected_root.bytes, msg.state_root, sizeof(bytes32_t));
}

void monad_statesync_client_handle_upsert(
    monad_statesync_client_context *const ctx, unsigned char const *const key,
    uint64_t const key_size, unsigned char const *const value,
    uint64_t const value_size, bool const code)
{
    byte_string_view const k(key, key_size);
    byte_string_view const v(value, value_size);

    if (code) {
        // code is immutable once inserted
        MONAD_ASSERT(value != nullptr);
        MONAD_ASSERT(key_size == sizeof(bytes32_t));
        bytes32_t hash;
        std::memcpy(hash.bytes, key, sizeof(bytes32_t));
        ctx->code.emplace(hash, v);
    }
    else {
        MONAD_ASSERT(value_size != 0 || value == nullptr);
        if (key_size == sizeof(bytes32_t)) {
            if (value == nullptr) {
                account_delete(ctx->state, ctx->db, k);
            }
            else {
                account_update(ctx->state, ctx->hash, k, v);
            }
        }
        else {
            MONAD_ASSERT(key_size == (sizeof(bytes32_t) * 2));
            if (value == nullptr) {
                storage_delete(ctx->state, ctx->db, k);
            }
            else {
                storage_update(ctx->state, ctx->db, k, v);
            }
        }
    }

    if ((++ctx->n_upserts % (1 << 20)) == 0) {
        commit(*ctx, ctx->db);
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
        commit(*ctx, ctx->db);
    }
}

bool monad_statesync_client_finalize(monad_statesync_client_context *const ctx)
{
    MONAD_ASSERT(ctx->state.empty());
    for (auto const &hash : ctx->hash) {
        if (hash == NULL_HASH) {
            continue;
        }
        auto const code = ctx->db.get(
            concat(CODE_NIBBLE, NibblesView{to_byte_string_view(hash.bytes)}),
            ctx->db.get_latest_block_id());
        MONAD_ASSERT(code.has_value());
        if (hash != std::bit_cast<bytes32_t>(keccak256(code.value()))) {
            return false;
        }
    }
    if (ctx->db.get_latest_block_id() != ctx->target) {
        ctx->db.move_trie_version_forward(ctx->current, ctx->target);
    }
    MONAD_ASSERT(ctx->target == ctx->db.get_latest_block_id());
    TrieDb db{ctx->db};
    return db.state_root() == ctx->expected_root;
}

void monad_statesync_client_context_destroy(
    monad_statesync_client_context *const ctx)
{
    delete ctx;
}
