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
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/fmt/bytes_fmt.hpp> // NOLINT
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/db/state_machine_init.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/state_machine_init.hpp>
#include <category/statesync/statesync_client.h>
#include <category/statesync/statesync_client_context.hpp>
#include <category/statesync/statesync_protocol.hpp>
#include <category/statesync/statesync_version.h>
#include <category/vm/evm/traits.hpp>

#include <algorithm>
#include <filesystem>
#include <optional>

using namespace monad;
using namespace monad::mpt;

unsigned const MONAD_SQPOLL_DISABLED = unsigned(-1);

monad_statesync_client_context *monad_statesync_client_context_create(
    monad_chain_config const chain_config,
    char const *const *const dbname_paths, size_t const len,
    unsigned const sq_thread_cpu, monad_statesync_client *const sync,
    void (*statesync_send_request)(
        monad_statesync_client *, monad_sync_request))
{
    std::vector<std::filesystem::path> const paths{
        dbname_paths, dbname_paths + len};
    MONAD_ASSERT(!paths.empty());
    // C ABI entry — runs in a foreign process; register the state machine
    // factories so the kind-driven Db ctor can resolve `ethereum`.
    // Idempotent: re-registration overwrites the prior factory.
    register_ethereum_state_machines();
    register_monad_state_machines();
    return new monad_statesync_client_context{
        chain_config,
        paths,
        sq_thread_cpu == MONAD_SQPOLL_DISABLED
            ? std::nullopt
            : std::make_optional(sq_thread_cpu),
        32,
        sync,
        statesync_send_request};
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
    if (ctx->tgrt.number == INVALID_BLOCK_NUM) {
        return false;
    }

    for (auto const &[n, _] : ctx->progress) {
        MONAD_ASSERT(n == INVALID_BLOCK_NUM || n <= ctx->tgrt.number);
        if (n != ctx->tgrt.number) {
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
    monad_statesync_client_context *const ctx, unsigned char const *const data,
    uint64_t const size)
{
    MONAD_ASSERT(std::ranges::all_of(
        ctx->protocol, [](auto const &ptr) { return ptr != nullptr; }))

    byte_string_view raw{data, size};
    auto const res = rlp::decode_block_header(raw);
    MONAD_ASSERT(res.has_value());
    auto const &tgrt = res.value();
    MONAD_ASSERT(tgrt.number != INVALID_BLOCK_NUM);
    MONAD_ASSERT(
        ctx->tgrt.number == INVALID_BLOCK_NUM ||
        tgrt.number >= ctx->tgrt.number);

    ctx->tgrt = tgrt;

    MONAD_ASSERT(
        tgrt.number, "genesis should be loaded manually without statesync");

    if (tgrt.number == ctx->db.get_latest_version()) {
        MONAD_ASSERT(monad_statesync_client_has_reached_target(ctx));
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
    MONAD_ASSERT(msg.n > progress || progress == INVALID_BLOCK_NUM);
    progress = msg.n;
    old_target = ctx->tgrt.number;

    if (progress != ctx->tgrt.number) {
        ctx->protocol.at(msg.prefix)->send_request(ctx, msg.prefix);
    }

    if (MONAD_UNLIKELY(monad_statesync_client_has_reached_target(ctx))) {
        ctx->commit();
    }
}

bool monad_statesync_client_finalize(monad_statesync_client_context *const ctx)
{
    auto const &tgrt = ctx->tgrt;
    MONAD_ASSERT(tgrt.number != INVALID_BLOCK_NUM);
    MONAD_ASSERT(ctx->deltas.empty());
    if (!ctx->buffered.empty()) {
        // sent storage with no account
        return false;
    }

    auto const latest_version = ctx->db.get_latest_version();
    // The dual-write keeps both timelines in lockstep, so the secondary must be
    // at the same version as the primary at finalize.
    if (ctx->secondary_db) {
        MONAD_ASSERT(
            latest_version == ctx->secondary_db->get_latest_version(),
            "dual-db versions should always be in sync");
    }

    MONAD_ASSERT(for_each_code(
        ctx->db, latest_version, [&](bytes32_t const &hash, byte_string_view) {
            ctx->seen_code.erase(hash);
        }));
    if (!ctx->seen_code.empty()) {
        // missing code
        return false;
    }

    // Roll one db forward from its synced version to the target, replaying the
    // trailing block headers. Applied to the primary and, in dual-db mode, the
    // page-encoded secondary, so both timelines are version-consistent at the
    // target.
    auto const roll_forward =
        [ctx, &tgrt, latest_version](mpt::Db &db) -> bool {
        if (latest_version != tgrt.number) {
            db.move_trie_version_forward(latest_version, tgrt.number);
            bytes32_t expected = tgrt.parent_hash;
            for (size_t i = 0; i < std::min(tgrt.number, 256ul); ++i) {
                auto const v = tgrt.number - i - 1;
                auto const &hdr = ctx->hdrs[v % ctx->hdrs.size()];
                auto const rlp = rlp::encode_block_header(hdr);
                auto const hash = to_bytes(keccak256(rlp));
                if (hash != expected) {
                    return false;
                }
                expected = hdr.parent_hash;

                Update block_header_update{
                    .key = block_header_nibbles,
                    .value = rlp,
                    .incarnation = true,
                    .next = UpdateList{},
                    .version = static_cast<int64_t>(v)};
                UpdateList updates;
                updates.push_front(block_header_update);
                Update finalized{
                    .key = finalized_nibbles,
                    .value = byte_string_view{},
                    .incarnation = false,
                    .next = std::move(updates),
                    .version = static_cast<int64_t>(v)};
                UpdateList finalized_updates;
                finalized_updates.push_front(finalized);
                db.upsert(
                    db.load_root_for_version(v),
                    std::move(finalized_updates),
                    v,
                    false,
                    false);
            }
        }
        return true;
    };

    if (!roll_forward(ctx->db)) {
        return false;
    }
    if (ctx->secondary_db && !roll_forward(*ctx->secondary_db)) {
        return false;
    }

    // Pick the right TrieDb to read state_root from based on the target's
    // revision.
    auto const monad_rev = ctx->chain->get_monad_revision(tgrt.timestamp);
    bool const page_encoded = mip_8_active(monad_rev);
    TrieDb *db = &ctx->tdb;
    if (page_encoded != db->is_page_encoded()) {
        MONAD_ASSERT_PRINTF(
            ctx->secondary_tdb &&
                ctx->secondary_tdb->is_page_encoded() == page_encoded,
            "No client db timeline is %s-encoded as the target revision "
            "requires",
            page_encoded ? "page" : "slot");
        db = ctx->secondary_tdb.get();
    }
    db->set_block_and_prefix(tgrt.number);
    if (auto const root = db->state_root(); root != tgrt.state_root) {
        LOG_WARNING(
            "statesync rejected target={}: state root mismatch, expected={} "
            "actual={}",
            tgrt.number,
            fmt::format("{}", tgrt.state_root),
            fmt::format("{}", root));
        return false;
    }

    ctx->db.update_finalized_version(tgrt.number);
    if (ctx->secondary_db) {
        ctx->secondary_db->update_finalized_version(tgrt.number);
    }
    return true;
}

void monad_statesync_client_context_destroy(
    monad_statesync_client_context *const ctx)
{
    delete ctx;
}
