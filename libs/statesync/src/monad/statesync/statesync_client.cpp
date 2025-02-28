#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>
#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/block.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/keccak.hpp>
#include <monad/core/likely.h>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/trie_db.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/genesis.hpp>
#include <monad/mpt/db_error.hpp>
#include <monad/mpt2/node.hpp>
#include <monad/mpt2/proof.hpp>
#include <monad/mpt2/rlp/item.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_protocol.hpp>
#include <monad/statesync/statesync_version.h>
#include <quill/Quill.h>
#include <quill/bundled/fmt/format.h>

#include <algorithm>
#include <filesystem>

using namespace monad;
using namespace monad::mpt;
using BOOST_OUTCOME_V2_NAMESPACE::success;

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
    if (ctx->tgrt.number == INVALID_BLOCK_ID) {
        return false;
    }

    for (auto const &[n, _] : ctx->progress) {
        MONAD_ASSERT(n == INVALID_BLOCK_ID || n <= ctx->tgrt.number);
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
    MONAD_ASSERT(tgrt.number != INVALID_BLOCK_ID);
    MONAD_ASSERT(
        ctx->tgrt.number == INVALID_BLOCK_ID ||
        tgrt.number >= ctx->tgrt.number);

    ctx->tgrt = tgrt;

    if (tgrt.number == ctx->db.get_latest_block_id()) {
        MONAD_ASSERT(monad_statesync_client_has_reached_target(ctx));
    }
    else if (tgrt.number == 0) {
        MONAD_ASSERT(ctx->db.get_latest_block_id() == INVALID_BLOCK_ID);
        read_genesis(ctx->genesis, ctx->tdb);
        ctx->progress.assign(
            ctx->progress.size(), {tgrt.number, INVALID_BLOCK_ID});
    }
    else {
        for (size_t i = 0; i < ctx->progress.size(); ++i) {
            ctx->protocol.at(i)->send_request(ctx, i);
        }
    }
}

Result<void> monad_statesync_client_verify_prefix(
    monad_statesync_client_context *const ctx, NibblesView const key,
    byte_string const &encoded_proof)
{
    BOOST_OUTCOME_TRY(
        monad::mpt2::verify_proof(key, ctx->tgrt.state_root, encoded_proof));

    auto version = ctx->db.get_latest_block_id();
    auto root = ctx->db.load_root_for_version(version);
    MONAD_ASSERT(root.is_valid());
    auto res =
        ctx->db.find(root, concat(finalized_nibbles, STATE_NIBBLE), version);
    MONAD_ASSERT(res.has_value());
    auto state_root = res.value();
    return ctx->db.verify_prefix_blocking(
        state_root, key, ComputeAccountLeaf::compute, encoded_proof);
}

bool monad_statesync_client_handle_upsert(
    monad_statesync_client_context *const ctx, uint64_t const prefix,
    monad_sync_type const type, unsigned char const *const val,
    uint64_t const size)
{
    return ctx->protocol.at(prefix)->handle_upsert(ctx, type, val, size);
}

bool monad_statesync_client_handle_done(
    monad_statesync_client_context *const ctx, monad_sync_done const msg)
{
    MONAD_ASSERT(msg.success);

    auto &[progress, old_target] = ctx->progress.at(msg.prefix);
    MONAD_ASSERT(msg.n > progress || progress == INVALID_BLOCK_ID);
    progress = msg.n;
    old_target = ctx->tgrt.number;

    if (progress != ctx->tgrt.number) {
        ctx->protocol.at(msg.prefix)->send_request(ctx, msg.prefix);
    }

    ctx->commit();

    return true;
}

void monad_statesync_client_handle_proof(
    monad_statesync_client_context *const ctx, uint64_t const prefix,
    unsigned char const *const data, uint64_t const size)
{
    ctx->proofs[prefix] = {data, data + size};
}

bool monad_statesync_client_finalize(monad_statesync_client_context *const ctx)
{
    auto const &tgrt = ctx->tgrt;
    MONAD_ASSERT(tgrt.number != INVALID_BLOCK_ID);
    MONAD_ASSERT(ctx->deltas.empty());
    if (!ctx->buffered.empty()) {
        // sent storage with no account
        return false;
    }
    else if (!ctx->pending.empty()) {
        // missing code
        return false;
    }

    auto failures = 0;
    // if not syncing to genesis, verify all prefixes
    if (tgrt.number != 0 && tgrt.number != ctx->db.get_latest_block_id()) {
        for (auto i = 0ul; i < monad_statesync_client_prefixes(); ++i) {
            auto bytes = from_prefix(i, monad_statesync_client_prefix_bytes());
            auto key = NibblesView{bytes};
            if (monad_statesync_client_verify_prefix(ctx, key, ctx->proofs[i])
                    .has_error()) {
                LOG_ERROR("prefix {} failed verification", i);
                ++failures;
            }
        }
    }
    if (failures != 0) {
        return false;
    }

    if (ctx->db.get_latest_block_id() != tgrt.number) {
        ctx->db.move_trie_version_forward(
            ctx->db.get_latest_block_id(), tgrt.number);
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
            ctx->db.upsert(std::move(finalized_updates), v, false, false);
        }
    }

    ctx->db.update_finalized_block(tgrt.number);

    TrieDb db{ctx->db};
    MONAD_ASSERT(db.get_block_number() == tgrt.number);

    return db.state_root() == tgrt.state_root;
}

void monad_statesync_client_context_destroy(
    monad_statesync_client_context *const ctx)
{
    delete ctx;
}
