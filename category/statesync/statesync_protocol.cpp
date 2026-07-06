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
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>

using namespace monad;
using namespace monad::mpt;

MONAD_ANONYMOUS_NAMESPACE_BEGIN

bytes32_t read_storage(
    monad_statesync_client_context &ctx, Address const &addr,
    bytes32_t const &key, std::optional<uint64_t> const domain)
{
    return ctx.tdb.read_storage(addr, Incarnation{0, 0}, key, domain);
}

bool decode_optional_domain(
    byte_string_view &raw, std::optional<uint64_t> &domain)
{
    if (raw.empty()) {
        return true;
    }
    auto const res = rlp::decode_unsigned<uint64_t>(raw);
    if (res.has_error() || res.value() == 0 || !raw.empty()) {
        return false;
    }
    domain = res.value();
    return true;
}

void account_update(
    monad_statesync_client_context &ctx, Address const &addr,
    std::optional<Account> const &acct, std::optional<uint64_t> const domain)
{
    using StorageDeltas = monad_statesync_client_context::StorageDeltas;
    auto &deltas = domain.has_value() ? ctx.domain_deltas[*domain] : ctx.deltas;
    auto &buffered =
        domain.has_value() ? ctx.domain_buffered[*domain] : ctx.buffered;

    if (acct.has_value()) {
        auto const &hash = acct.value().code_hash;
        if (hash != NULL_HASH) {
            ctx.seen_code.emplace(hash);
        }
    }

    auto const it = deltas.find(addr);
    auto const updated = it != deltas.end();

    if (buffered.contains(addr)) {
        MONAD_ASSERT(
            !ctx.tdb.read_account(addr, domain).has_value() && !updated);
        if (acct.has_value()) {
            MONAD_ASSERT(
                deltas
                    .emplace(
                        addr,
                        std::make_pair(
                            acct.value(), std::move(buffered.at(addr))))
                    .second);
        }
        buffered.erase(addr);
    }
    else if (!updated) {
        if (acct.has_value()) {
            MONAD_ASSERT(
                deltas
                    .emplace(
                        addr, std::make_pair(acct.value(), StorageDeltas{}))
                    .second);
        }
        else if (ctx.tdb.read_account(addr, domain).has_value()) {
            MONAD_ASSERT(deltas.emplace(addr, std::nullopt).second);
        }
    }
    // incarnation
    else if (acct.has_value() && !it->second.has_value()) {
        ctx.commit();
        account_update(ctx, addr, acct, domain);
    }
    else if (acct.has_value()) {
        std::get<Account>(it->second.value()) = acct.value();
    }
    else if (ctx.tdb.read_account(addr, domain).has_value()) {
        it->second = std::nullopt;
    }
    else {
        deltas.erase(it);
    }
}

void storage_update(
    monad_statesync_client_context &ctx, Address const &addr,
    bytes32_t const &key, bytes32_t const &val,
    std::optional<uint64_t> const domain)
{
    using StorageDeltas = monad_statesync_client_context::StorageDeltas;
    auto &deltas = domain.has_value() ? ctx.domain_deltas[*domain] : ctx.deltas;
    auto &buffered =
        domain.has_value() ? ctx.domain_buffered[*domain] : ctx.buffered;

    auto const it = deltas.find(addr);
    auto const updated = it != deltas.end();

    if (buffered.contains(addr)) {
        MONAD_ASSERT(
            !ctx.tdb.read_account(addr, domain).has_value() && !updated);
        if (val == bytes32_t{}) {
            buffered[addr].erase(key);
            if (buffered[addr].empty()) {
                buffered.erase(addr);
            }
        }
        else {
            auto const sit = buffered[addr].find(key);
            if (sit != buffered[addr].end()) {
                sit->second = val;
            }
            else {
                MONAD_ASSERT(buffered[addr].emplace(key, val).second);
            }
        }
    }
    else if (
        val != bytes32_t{} ||
        read_storage(ctx, addr, key, domain) != bytes32_t{}) {
        if (updated) {
            if (it->second.has_value()) {
                std::get<StorageDeltas>(it->second.value())[key] = val;
            }
            // incarnation
            else if (val != bytes32_t{}) {
                ctx.commit();
                storage_update(ctx, addr, key, val, domain);
            }
        }
        else {
            auto const orig = ctx.tdb.read_account(addr, domain);
            if (orig.has_value()) {
                MONAD_ASSERT(
                    deltas
                        .emplace(
                            addr,
                            std::make_pair(
                                orig.value(), StorageDeltas{{key, val}}))
                        .second);
            }
            else {
                MONAD_ASSERT(val != bytes32_t{});
                MONAD_ASSERT(
                    buffered.emplace(addr, StorageDeltas{{key, val}}).second);
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
        std::optional<uint64_t> domain;
        if (res.has_error() || !decode_optional_domain(raw, domain)) {
            return false;
        }
        auto [addr, acct] = res.value();
        acct.incarnation = Incarnation{0, 0};
        account_update(*ctx, addr, acct, domain);
    }
    else if (type == SYNC_TYPE_UPSERT_STORAGE) {
        if (size < sizeof(Address)) {
            return false;
        }
        raw.remove_prefix(sizeof(Address));
        // Use the raw decoder so any trailing bytes remain available for the
        // optional domain suffix.
        auto const res = decode_storage_db_raw(raw);
        std::optional<uint64_t> domain;
        // The compact key/value must fit before to_bytes(), and any remaining
        // payload must decode as a valid optional domain.
        if (res.has_error() || res.value().first.size() > sizeof(bytes32_t) ||
            res.value().second.size() > sizeof(bytes32_t) ||
            !decode_optional_domain(raw, domain)) {
            return false;
        }
        storage_update(
            *ctx,
            unaligned_load<Address>(val),
            to_bytes(res.value().first),
            to_bytes(res.value().second),
            domain);
    }
    else if (type == SYNC_TYPE_UPSERT_ACCOUNT_DELETE) {
        if (size < sizeof(Address)) {
            return false;
        }
        raw.remove_prefix(sizeof(Address));
        std::optional<uint64_t> domain;
        if (!decode_optional_domain(raw, domain)) {
            return false;
        }
        account_update(
            *ctx, unaligned_load<Address>(val), std::nullopt, domain);
    }
    else if (type == SYNC_TYPE_UPSERT_STORAGE_DELETE) {
        if (size < sizeof(Address)) {
            return false;
        }
        raw.remove_prefix(sizeof(Address));
        auto const res = rlp::decode_bytes32_compact(raw);
        std::optional<uint64_t> domain;
        if (res.has_error() || !decode_optional_domain(raw, domain)) {
            return false;
        }
        storage_update(
            *ctx, unaligned_load<Address>(val), res.value(), {}, domain);
    }
    else {
        MONAD_ASSERT(type == SYNC_TYPE_UPSERT_HEADER);
        auto const res = rlp::decode_block_header(raw);
        if (res.has_error() || !raw.empty()) {
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
