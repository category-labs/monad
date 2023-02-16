#include <monad/execution/interhash.hpp>

#include <utility>

#include <absl/container/btree_set.h>

#include <silkworm/common/assert.hpp>
#include <silkworm/common/endian.hpp>
#include <silkworm/common/lru_cache.hpp>
#include <silkworm/common/rlp_err.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/trie/nibbles.hpp>

namespace silkworm::stagedsync {

StageResult MonadInterHashes::forward(db::RWTxn& txn) {
    StageResult ret{StageResult::kSuccess};

    auto hashstate_stage_progress{db::stages::read_stage_progress(*txn, db::stages::kHashStateKey)};
    
    auto const header{db::read_header_by_number(block_db_, hashstate_stage_progress)};
    SILKWORM_ASSERT(header.has_value());
    auto expected_state_root{header->state_root};

    ret = increment_intermediate_hashes(txn, hashstate_stage_progress, &expected_state_root);
    db::stages::write_stage_progress(*txn, db::stages::kIntermediateHashesKey, hashstate_stage_progress);
    txn.commit();

    return ret;
}

trie::PrefixSet MonadInterHashes::collect_account_changes(db::RWTxn& txn, BlockNum curr_block_num,
                                                     absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses) {
    absl::btree_set<Bytes> deleted_ts_prefixes{};
    silkworm::lru_cache<evmc::address, std::optional<Account>> plainstate_accounts(100'000);

    const Bytes starting_key{db::block_key(curr_block_num)};
    trie::PrefixSet ret;

    db::Cursor account_changeset(txn, db::table::kAccountChangeSet);
    db::Cursor plain_state(txn, db::table::kPlainState);

    auto changeset_data{account_changeset.lower_bound(db::to_slice(starting_key), /*throw_notfound=*/false)};
    while (changeset_data) {
        auto changeset_value_view{db::from_slice(changeset_data.value)};

        // Extract address and hash if needed
        const evmc::address address{to_evmc_address(changeset_value_view)};
        changeset_value_view.remove_prefix(kAddressLength);
        auto hashed_addresses_it{hashed_addresses.find(address)};
        if (hashed_addresses_it == hashed_addresses.end()) {
            const auto hashed_address{keccak256(address)};
            hashed_addresses_it = hashed_addresses.insert_or_assign(address, hashed_address).first;
        }

        // Lookup value in plainstate if any
        // Note ! on unwinds plainstate has not been unwound yet.
        std::optional<Account> plainstate_account{};
        if (auto item{plainstate_accounts.get(address)}; item != nullptr) {
            plainstate_account = *item;
        } else {
            auto ps_data{plain_state.find(db::to_slice(address.bytes), false)};
            if (ps_data && ps_data.value.length()) {
                auto [account, rlp_err]{Account::from_encoded_storage(db::from_slice(ps_data.value))};
                rlp::success_or_throw(rlp_err);
                plainstate_account.emplace(account);
            }
            plainstate_accounts.put(address, plainstate_account);
        }

        bool account_created{false};  // Whether the account has to be marked as created in changed list

        // For forward collection:
        // Creation : if there is no value in changeset it means the account has been created
        // TrieStorage cleanup : if there is value in changeset we check account in changeset matches account in
        // plainstate Specifically if both have value and incarnations do not match then a self-destruct has
        // happened (with possible recreation). If they don't match delete from TrieStorage all hashed addresses
        // + incarnation
        if (!changeset_value_view.empty()) {
            auto [changeset_account, rlp_err]{Account::from_encoded_storage(changeset_value_view)};
            rlp::success_or_throw(rlp_err);
            if (changeset_account.incarnation) {
                if (plainstate_account == std::nullopt ||
                    plainstate_account->incarnation != changeset_account.incarnation) {
                    (void)deleted_ts_prefixes.insert(
                        db::storage_prefix(address.bytes, changeset_account.incarnation));
                }
            }
        } else {
            account_created = true;
        }

        ret.insert(trie::unpack_nibbles(hashed_addresses_it->second.bytes), account_created);
        changeset_data = account_changeset.to_current_next_multi(/*throw_notfound=*/false);
    }

    // Eventually delete nodes from trie for deleted accounts
    if (!deleted_ts_prefixes.empty()) {
        db::Cursor trie_storage(txn, db::table::kTrieOfStorage);
        for (const auto& prefix : deleted_ts_prefixes) {
            const auto prefix_slice{db::to_slice(prefix)};
            auto data{trie_storage.lower_bound(prefix_slice, /*throw_notfound=*/false)};
            while (data && data.key.starts_with(prefix_slice)) {
                trie_storage.erase();
                data = trie_storage.to_next(/*throw_notfound=*/false);
            }
        }
    }
    return ret;
}

trie::PrefixSet MonadInterHashes::collect_storage_changes(db::RWTxn& txn, BlockNum curr_block_num,
                                                     absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses) {
    const Bytes starting_key{db::block_key(curr_block_num)};
    trie::PrefixSet ret;

    // Don't rehash same addresses
    absl::btree_map<evmc::address, ethash_hash256>::iterator hashed_addresses_it{hashed_addresses.begin()};

    db::Cursor storage_changeset(txn, db::table::kStorageChangeSet);
    auto changeset_data{storage_changeset.lower_bound(db::to_slice(starting_key), /*throw_notfound=*/false)};

    while (changeset_data) {
        auto changeset_key_view{db::from_slice(changeset_data.key)};
        changeset_key_view.remove_prefix(sizeof(BlockNum));

        const evmc::address address{to_evmc_address(changeset_key_view)};
        hashed_addresses_it = hashed_addresses.find(address);
        if (hashed_addresses_it == hashed_addresses.end()) {
            const auto hashed_address{keccak256(address.bytes)};
            hashed_addresses_it = hashed_addresses.insert_or_assign(address, hashed_address).first;
        }

        changeset_key_view.remove_prefix(kAddressLength);

        Bytes hashed_key(db::kHashedStoragePrefixLength + (2 * kHashLength), '\0');
        std::memcpy(&hashed_key[0], hashed_addresses_it->second.bytes, kHashLength);
        std::memcpy(&hashed_key[kHashLength], changeset_key_view.data(), db::kIncarnationLength);

        while (changeset_data) {
            auto changeset_value_view{db::from_slice(changeset_data.value)};

            const ByteView location{changeset_value_view.substr(0, kHashLength)};
            const auto hashed_location{keccak256(location)};

            auto unpacked_location{trie::unpack_nibbles(hashed_location.bytes)};
            std::memcpy(&hashed_key[db::kHashedStoragePrefixLength], unpacked_location.data(),
                        unpacked_location.length());
            auto ret_item{ByteView(hashed_key.data(), db::kHashedStoragePrefixLength + unpacked_location.length())};

            ret.insert(ret_item, changeset_value_view.length() == kHashLength);
            changeset_data = storage_changeset.to_current_next_multi(/*throw_notfound=*/false);
        }

        changeset_data = storage_changeset.to_next(/*throw_notfound=*/false);
    }

    return ret;
}

StageResult MonadInterHashes::increment_intermediate_hashes(db::RWTxn& txn, BlockNum curr_block_num,
                                                       const evmc::bytes32* expected_root) {
    StageResult ret{StageResult::kSuccess};

    account_collector_ = std::make_unique<etl::Collector>(node_settings_);
    storage_collector_ = std::make_unique<etl::Collector>(node_settings_);

    // Cache of hashed addresses
    absl::btree_map<evmc::address, ethash_hash256> hashed_addresses{};
    // Collect all changes from changesets
    trie::PrefixSet account_changes{collect_account_changes(txn, curr_block_num, hashed_addresses)};
    trie::PrefixSet storage_changes{collect_storage_changes(txn, curr_block_num, hashed_addresses)};
    // Remove unneeded RAM occupation
    hashed_addresses.clear();

    trie_loader_ = std::make_unique<trie::TrieLoader>(*txn, &account_changes, &storage_changes,
                                                        account_collector_.get(), storage_collector_.get());
    const evmc::bytes32 computed_root{trie_loader_->calculate_root()};

    // Fail if not what expected
    if (expected_root != nullptr && computed_root != *expected_root) {
        trie_loader_.reset();        // Don't need anymore
        account_collector_.reset();  // Will invoke dtor which causes all flushed files (if any) to be deleted
        storage_collector_.reset();  // Will invoke dtor which causes all flushed files (if any) to be deleted
        log::Error("Wrong trie root",
                    {"expected", to_hex(*expected_root, true), "got", to_hex(computed_root, true)});
        return StageResult::kWrongStateRoot;
    }

    flush_collected_nodes(txn);
    return ret;
}

void MonadInterHashes::flush_collected_nodes(db::RWTxn& txn) {
    // Proceed with loading of newly generated nodes and deletion of obsolete ones.
    trie_loader_.reset();
    loading_collector_ = std::move(account_collector_);

    db::Cursor target(txn, db::table::kTrieOfAccounts);
    MDBX_put_flags_t flags{target.empty() ? MDBX_put_flags_t::MDBX_APPEND : MDBX_put_flags_t::MDBX_UPSERT};
    loading_collector_->load(target, nullptr, flags);

    loading_collector_ = std::move(storage_collector_);

    target.bind(txn, db::table::kTrieOfStorage);
    flags = target.empty() ? MDBX_put_flags_t::MDBX_APPEND : MDBX_put_flags_t::MDBX_UPSERT;
    loading_collector_->load(target, nullptr, flags);

    loading_collector_.reset();
}

// glee: removed in next commit
std::vector<std::string> MonadInterHashes::get_log_progress() { return {}; }

}  // namespace silkworm::stagedsync