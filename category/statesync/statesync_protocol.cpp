#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bytes32_t read_storage(
    monad_statesync_client_context &ctx, Address const &addr,
    bytes32_t const &key)
{
    return ctx.tdb.read_storage(addr, Incarnation{0, 0}, key);
}

void account_update(
    monad_statesync_client_context &ctx, Address const &addr,
    std::optional<Account> const &acct)
{
    using StorageDeltas = monad_statesync_client_context::StorageDeltas;

    if (acct.has_value()) {
        auto const &hash = acct.value().code_hash;
        if (hash != NULL_HASH) {
            ctx.seen_code.emplace(hash);
        }
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
        ctx.commit();
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
                ctx.commit();
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

MONAD_NAMESPACE_BEGIN

void StatesyncProtocolV1::send_request(
    monad_statesync_client_context *const ctx, uint64_t const prefix) const
{
    auto const tgrt = ctx->tgrt.number;
    auto const &[progress, old_target] = ctx->progress[prefix];
    MONAD_ASSERT(progress == INVALID_BLOCK_NUM || progress < tgrt);
    MONAD_ASSERT(old_target == INVALID_BLOCK_NUM || old_target <= tgrt);
    auto const from = progress == INVALID_BLOCK_NUM ? 0 : progress + 1;
    ctx->statesync_send_request(
        ctx->sync,
        monad_sync_request{
            .prefix = prefix,
            .prefix_bytes = monad_statesync_client_prefix_bytes(),
            .target = tgrt,
            .from = from,
            .until = from >= (tgrt * 99 / 100) ? tgrt : tgrt * 99 / 100,
            .old_target = old_target});
}

bool StatesyncProtocolV1::handle_upsert(
    monad_statesync_client_context *const ctx, monad_sync_type const type,
    unsigned char const *const val, uint64_t const size) const
{
    byte_string_view raw{val, size};
    if (type == SYNC_TYPE_UPSERT_CODE) {
        // code is immutable once inserted - no deletions
        ctx->code.emplace(std::bit_cast<bytes32_t>(keccak256(raw)), raw);
    }
    else if (type == SYNC_TYPE_UPSERT_ACCOUNT) {
        auto const res = decode_account_db(raw);
        if (res.has_error()) {
            return false;
        }
        auto [addr, acct] = res.value();
        acct.incarnation = Incarnation{0, 0};
        account_update(*ctx, addr, acct);
    }
    else if (type == SYNC_TYPE_UPSERT_STORAGE) {
        if (size < sizeof(Address)) {
            return false;
        }
        raw.remove_prefix(sizeof(Address));
        auto const res = decode_storage_db(raw);
        if (res.has_error()) {
            return false;
        }
        auto const &[k, v] = res.value();
        storage_update(*ctx, unaligned_load<Address>(val), k, v);
    }
    else if (type == SYNC_TYPE_UPSERT_ACCOUNT_DELETE) {
        if (size != sizeof(Address)) {
            return false;
        }
        account_update(*ctx, unaligned_load<Address>(val), std::nullopt);
    }
    else if (type == SYNC_TYPE_UPSERT_STORAGE_DELETE) {
        if (size < sizeof(Address)) {
            return false;
        }
        raw.remove_prefix(sizeof(Address));
        auto const res = rlp::decode_bytes32_compact(raw);
        if (res.has_error()) {
            return false;
        }
        storage_update(*ctx, unaligned_load<Address>(val), res.value(), {});
    }
    else {
        MONAD_ASSERT(type == SYNC_TYPE_UPSERT_HEADER);
        auto const res = rlp::decode_block_header(raw);
        if (res.has_error()) {
            return false;
        }
        ctx->hdrs[res.value().number % ctx->hdrs.size()] = res.value();
    }

    if ((++ctx->n_upserts % (1 << 20)) == 0) {
        ctx->commit();
    }

    return true;
}

MONAD_NAMESPACE_END
