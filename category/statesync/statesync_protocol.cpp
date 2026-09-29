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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/log.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

#include <utility>

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
    else {
        // Deleting the account voids its pending storage, in branches below
        // that do not commit. Coverage granted against those slots must not
        // outlive them, or a later partial page would be built from scratch.
        ctx.covered_pages.erase(addr);
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
    // The account was deleted earlier in this batch and is now recreated.
    // Flush the deletion first so the new one starts from an empty subtrie;
    // after the flush this batch holds nothing for the address.
    else if (acct.has_value() && !it->second.has_value()) {
        ctx.commit();
        MONAD_ASSERT(
            ctx.deltas
                .emplace(addr, std::make_pair(acct.value(), StorageDeltas{}))
                .second);
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
            // Storage for an account this batch has pending deletion. Flush
            // the deletion first; the account is then gone from the trie, so
            // the slot waits in `buffered` for the record that recreates it.
            else if (val != bytes32_t{}) {
                ctx.commit();
                MONAD_ASSERT(!ctx.tdb.read_account(addr).has_value());
                MONAD_ASSERT(
                    ctx.buffered.emplace(addr, StorageDeltas{{key, val}})
                        .second);
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

void StatesyncProtocolV1_2::send_request(
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
            .old_target = old_target,
            .version = version_});
}

bool StatesyncProtocolV1_2::apply_upsert(
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
        if (res.has_error() || !raw.empty()) {
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
        if (res.has_error() || !raw.empty()) {
            return false;
        }
        storage_update(*ctx, unaligned_load<Address>(val), res.value(), {});
    }
    else {
        if (type != SYNC_TYPE_UPSERT_HEADER) {
            return false;
        }
        auto const res = rlp::decode_block_header(raw);
        if (res.has_error() || !raw.empty()) {
            return false;
        }
        ctx->hdrs[res.value().number % ctx->hdrs.size()] = res.value();
    }

    return true;
}

bool StatesyncProtocolV1_2::handle_upsert(
    monad_statesync_client_context *const ctx, monad_sync_type const type,
    unsigned char const *const val, uint64_t const size) const
{
    if (!apply_upsert(ctx, type, val, size)) {
        // Rejecting a record aborts the node: bft asserts on this return value
        // and its release profile aborts on panic. This log is the only place
        // the offending record is named.
        LOG_ERROR(
            "statesync client rejected upsert type={} size={}",
            std::to_underlying(type),
            size);
        return false;
    }
    MONAD_ASSERT(ctx->upserts_per_commit != 0);
    // Threshold rather than modulo: a page record advances the counter by more
    // than one, so an exact multiple cannot be relied on.
    if (++ctx->n_upserts >= ctx->upserts_per_commit) {
        ctx->commit();
    }
    return true;
}

bool StatesyncProtocolV1_3::apply_upsert(
    monad_statesync_client_context *const ctx, monad_sync_type const type,
    unsigned char const *const val, uint64_t const size) const
{
    if (type != SYNC_TYPE_UPSERT_STORAGE_PAGE) {
        return StatesyncProtocolV1_2::apply_upsert(ctx, type, val, size);
    }
    if (size < sizeof(Address)) {
        return false;
    }
    byte_string_view leaf{val, size};
    leaf.remove_prefix(sizeof(Address));
    auto const decoded = decode_storage_page_leaf(leaf);
    if (decoded.has_error()) {
        LOG_ERROR("statesync client could not decode storage page leaf");
        return false;
    }
    auto const &page = decoded.value().page;
    // An empty page would grant coverage while contributing no slot. A
    // slot-granular delete arriving for that page in the same commit window
    // would then build it from empty and delete the whole page entry, losing
    // every slot the client holds on disk for it.
    if (page.is_empty()) {
        LOG_ERROR("statesync client rejected empty storage page record");
        return false;
    }
    auto const addr = unaligned_load<Address>(val);
    for (auto const [slot_key, slot_val] : decoded.value().slots()) {
        storage_update(*ctx, addr, slot_key, slot_val);
    }
    // Granted after the loop: storage_update can commit on an incarnation
    // conflict, and that commit clears coverage.
    ctx->covered_pages[addr].emplace(decoded.value().page_key);
    // handle_upsert counts this record once; the page's remaining slots are
    // deltas the commit window has to bound too.
    ctx->n_upserts += page.size() - 1;
    return true;
}

MONAD_NAMESPACE_END
