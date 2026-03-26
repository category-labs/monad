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
#include <category/core/unaligned.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/storage_encoding.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

byte_string read_storage(
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
    bytes32_t const &key, byte_string val)
{
    using StorageDeltas = monad_statesync_client_context::StorageDeltas;

    auto const it = ctx.deltas.find(addr);
    auto const updated = it != ctx.deltas.end();

    if (ctx.buffered.contains(addr)) {
        MONAD_ASSERT(!ctx.tdb.read_account(addr).has_value() && !updated);
        if (val.empty()) {
            ctx.buffered[addr].erase(key);
            if (ctx.buffered[addr].empty()) {
                ctx.buffered.erase(addr);
            }
        }
        else {
            auto const sit = ctx.buffered[addr].find(key);
            if (sit != ctx.buffered[addr].end()) {
                sit->second = std::move(val);
            }
            else {
                MONAD_ASSERT(
                    ctx.buffered[addr].emplace(key, std::move(val)).second);
            }
        }
    }
    else if (!val.empty() || !read_storage(ctx, addr, key).empty()) {
        if (updated) {
            if (it->second.has_value()) {
                std::get<StorageDeltas>(it->second.value())[key] =
                    std::move(val);
            }
            // incarnation
            else if (!val.empty()) {
                ctx.commit();
                storage_update(ctx, addr, key, std::move(val));
            }
        }
        else {
            auto const orig = ctx.tdb.read_account(addr);
            if (orig.has_value()) {
                MONAD_ASSERT(ctx.deltas
                                 .emplace(
                                     addr,
                                     std::make_pair(
                                         orig.value(),
                                         StorageDeltas{{key, std::move(val)}}))
                                 .second);
            }
            else {
                MONAD_ASSERT(!val.empty());
                MONAD_ASSERT(
                    ctx.buffered
                        .emplace(addr, StorageDeltas{{key, std::move(val)}})
                        .second);
            }
        }
    }
    else if (updated && it->second.has_value()) {
        MONAD_ASSERT(val.empty());
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
        byte_string_view const raw_before{raw};
        auto const res = decode_storage_db(raw);
        if (res.has_error()) {
            return false;
        }
        auto const consumed = raw_before.size() - raw.size();
        storage_update(
            *ctx,
            unaligned_load<Address>(val),
            res.value().first,
            byte_string{raw_before.data(), consumed});
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
        auto const &key = res.value();
        auto const addr = unaligned_load<Address>(val);

        if (ctx->machine.storage_format() == mpt::StorageFormat::PageCOO) {
            // Page format: the deletion key is a slot preimage. Read the
            // containing page, zero the specific slot, and write back the
            // modified page (or delete the page entry if now empty).
            // Check buffered deltas first to avoid losing uncommitted
            // modifications (e.g. prior deletions on the same page).
            auto const page_key = compute_page_key(key);
            auto const offset = compute_slot_offset(key);

            // Resolve the current page value. Buffered deltas hold full
            // RLP trie leaf values; tdb.read_storage returns the inner
            // value (after RLP unwrap). Unwrap buffered values before
            // decoding the page.
            byte_string page_enc;
            auto const dit = ctx->deltas.find(addr);
            if (dit != ctx->deltas.end() && dit->second.has_value()) {
                auto const &sd = dit->second.value().second;
                auto const sit = sd.find(page_key);
                if (sit != sd.end() && !sit->second.empty()) {
                    byte_string_view v{sit->second};
                    auto const r = decode_storage_db(v);
                    if (r.has_value()) {
                        page_enc = byte_string{
                            r.value().second.data(), r.value().second.size()};
                    }
                }
            }
            if (page_enc.empty() && ctx->buffered.contains(addr)) {
                auto const sit = ctx->buffered[addr].find(page_key);
                if (sit != ctx->buffered[addr].end() && !sit->second.empty()) {
                    byte_string_view v{sit->second};
                    auto const r = decode_storage_db(v);
                    if (r.has_value()) {
                        page_enc = byte_string{
                            r.value().second.data(), r.value().second.size()};
                    }
                }
            }
            if (page_enc.empty()) {
                page_enc =
                    ctx->tdb.read_storage(addr, Incarnation{0, 0}, page_key);
            }

            if (!page_enc.empty()) {
                auto page = decode_storage_page(page_enc);
                page[offset] = bytes32_t{};
                if (page.is_empty()) {
                    storage_update(*ctx, addr, page_key, byte_string{});
                }
                else {
                    storage_update(
                        *ctx,
                        addr,
                        page_key,
                        encode_storage_page_db(page_key, page));
                }
            }
        }
        else {
            storage_update(*ctx, addr, key, byte_string{});
        }
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
