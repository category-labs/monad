#include <monad/core/block.hpp>
#include <monad/core/rlp/block_rlp.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/update.hpp>
#include <monad/statesync/statesync_client.h>
#include <monad/statesync/statesync_client_context.hpp>
#include <monad/statesync/statesync_protocol.hpp>

#include <deque>
#include <sys/sysinfo.h>

using namespace monad;
using namespace monad::mpt;

monad_statesync_client_context::monad_statesync_client_context(
    std::vector<std::filesystem::path> const dbname_paths,
    std::filesystem::path const genesis,
    std::optional<unsigned> const sq_thread_cpu,
    monad_statesync_client *const sync,
    void (*statesync_send_request)(
        struct monad_statesync_client *, struct monad_sync_request))
    : db{machine,
         mpt::OnDiskDbConfig{
             .append = true,
             .compaction = false,
             .rewind_to_latest_finalized = true,
             .rd_buffers = 8192,
             .wr_buffers = 32,
             .uring_entries = 128,
             .sq_thread_cpu = sq_thread_cpu,
             .dbname_paths = dbname_paths}}
    , tdb{db} // open with latest finalized if valid, otherwise init as block 0
    , progress(
          monad_statesync_client_prefixes(),
          {db.get_latest_block_id(), db.get_latest_block_id()})
    , protocol(monad_statesync_client_prefixes())
    , tgrt{BlockHeader{.number = mpt::INVALID_BLOCK_ID}}
    , current{db.get_latest_block_id() == mpt::INVALID_BLOCK_ID ? 0 : db.get_latest_block_id() + 1}
    , n_upserts{0}
    , genesis{genesis}
    , sync{sync}
    , statesync_send_request{statesync_send_request}
{
    MONAD_ASSERT(
        db.get_latest_block_id() == db.get_latest_finalized_block_id());
}

void monad_statesync_client_context::commit()
{
    std::deque<mpt::Update> alloc;
    std::deque<byte_string> bytes_alloc;
    std::deque<hash256> hash_alloc;
    UpdateList accounts;
    for (auto const &[addr, delta] : deltas) {
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
                    .version = static_cast<int64_t>(current)}));
            }
        }
        accounts.push_front(alloc.emplace_back(Update{
            .key = hash_alloc.emplace_back(keccak256(addr.bytes)),
            .value = value,
            .incarnation = false,
            .next = std::move(storage),
            .version = static_cast<int64_t>(current)}));
    }
    UpdateList code_updates;

    fprintf(stderr, "client commit accounts %ld\n", accounts.size());

    std::deque<bytes32_t> upserted;
    for (auto const &hash : pending) {
        if (code.contains(hash)) {
            code_updates.push_front(alloc.emplace_back(Update{
                .key = NibblesView{hash},
                .value = code.at(hash),
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(current)}));
            upserted.emplace_back(hash);
        }
    }

    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(accounts),
        .version = static_cast<int64_t>(current)};
    auto code_update = Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(current)};
    auto const rlp = rlp::encode_block_header(tgrt);
    auto block_header_update = Update{
        .key = block_header_nibbles,
        .value = rlp,
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};
    UpdateList updates;
    updates.push_front(state_update);
    updates.push_front(code_update);
    updates.push_front(block_header_update);

    UpdateList finalized_updates;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates),
        .version = static_cast<int64_t>(current)};
    finalized_updates.push_front(finalized);

    db.upsert(std::move(finalized_updates), current, false, false);
    tdb.set_block_and_round(current);
    for (auto const &hash : upserted) {
        MONAD_ASSERT(this->upserted.emplace(hash).second);
        MONAD_ASSERT(pending.erase(hash) == 1);
        MONAD_ASSERT(code.erase(hash) == 1);
    }
    deltas.clear();
}

namespace
{
    void delete_prefix(monad::mpt::Db &db, NibblesView prefix, uint64_t version)
    {
        auto state_root =
            db.find(concat(finalized_nibbles, STATE_NIBBLE), version);
        MONAD_ASSERT(state_root.has_value());
        auto res = db.find_prefix(state_root.value(), prefix, version);
        if (res.second != find_result::success &&
            res.second != find_result::key_ends_earlier_than_node_failure) {
            std::cerr << "deleting prefix " << prefix << " not found"
                      << std::endl;
            // Prefix already does not exist
            return;
        }
        auto delete_key = concat(
            prefix,
            NibblesView(
                res.first.prefix_index,
                res.first.node->path_nibble_index_end,
                res.first.node->path_data()));
        Update prefix_delete = Update{
            .key = delete_key,
            .value = std::nullopt,
            .incarnation = false,
            .prefix_update = true,
            .next = UpdateList{},
            .version = static_cast<int64_t>(version)};
        UpdateList deletes;
        deletes.push_front(prefix_delete);

        auto state_update = Update{
            .key = state_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(deletes),
            .version = static_cast<int64_t>(version)};

        UpdateList updates;
        updates.push_front(state_update);

        UpdateList finalized_updates;
        Update finalized{
            .key = finalized_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(updates),
            .version = static_cast<int64_t>(version)};
        finalized_updates.push_front(finalized);

        db.upsert(std::move(finalized_updates), version, false, false);
    }
}

void monad_statesync_client_context::restore_prefix(NibblesView prefix)
{
    std::cerr << "deleting prefix " << prefix << std::endl;
    delete_prefix(db, prefix, current);
    if (current == 0) {
        // Sync from genesis, prefix did not exist
        return;
    }
    std::cerr << "restoring prefix " << prefix << " current " << current
              << std::endl;
    auto root = db.load_root_for_version(current - 1);
    MONAD_ASSERT(root.is_valid());
    auto state_root =
        db.find(concat(finalized_nibbles, STATE_NIBBLE), current - 1);
    MONAD_ASSERT(state_root.has_value());
    auto res = db.find_prefix(state_root.value(), prefix, current - 1);
    if (res.second != find_result::success &&
        res.second != find_result::key_ends_earlier_than_node_failure) {
        // Prefix does not exist before state sync
        return;
    }
    auto node = res.first.node;
    if (node->number_of_children() == 1) {
        // Special case, compute requires the child pointer for single child
        auto child_res = db.find_prefix(
            NodeCursor{*node, node->path_nibble_index_end},
            concat((unsigned char)std::countr_zero(node->mask)),
            current - 1);
        MONAD_ASSERT(
            child_res.second == find_result::success ||
            child_res.second ==
                find_result::key_ends_earlier_than_node_failure);
        auto child = child_res.first.node;
        node->set_next(
            0,
            make_node(
                *child,
                child->path_nibble_view(),
                child->opt_value(),
                child->version));
    }

    auto update_key = concat(
        prefix,
        NibblesView(
            res.first.prefix_index,
            res.first.node->path_nibble_index_end,
            res.first.node->path_data()));
    Update prefix_update = Update{
        .key = update_key,
        .value = std::nullopt,
        .incarnation = false,
        .prefix_update = true,
        .node = make_node(
            *node, node->path_nibble_view(), node->opt_value(), node->version),
        .next = UpdateList{},
        .version = static_cast<int64_t>(current)};

    UpdateList prefix_updates;
    prefix_updates.push_front(prefix_update);

    auto state_update = Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(prefix_updates),
        .version = static_cast<int64_t>(current)};
    UpdateList updates;
    updates.push_front(state_update);

    UpdateList finalized_updates;
    Update finalized{
        .key = finalized_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates),
        .version = static_cast<int64_t>(current)};
    finalized_updates.push_front(finalized);

    db.upsert(std::move(finalized_updates), current, false, false);
}
