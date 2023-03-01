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

StageResult MonadInterHashes::run(db::RWTxn& txn, monad::BlockDb const &block_db, db::MonadBuffer &buffer, silkworm::BlockNum block_num) {
    StageResult ret{StageResult::kSuccess};

    assert(db::stages::read_stage_progress(*txn, db::stages::kIntermediateHashesKey) < block_num);
    
    auto const header{silkworm::db::read_header_by_number(block_db, block_num)};
    SILKWORM_ASSERT(header.has_value());
    auto expected_state_root{header->state_root};

    ret = increment_intermediate_hashes(txn, buffer, block_num, &expected_state_root);
    db::stages::write_stage_progress(*txn, db::stages::kIntermediateHashesKey, block_num);
    txn.commit();

    return ret;
}

trie::PrefixSet MonadInterHashes::collect_account_changes(db::RWTxn& txn, db::MonadBuffer &buffer, [[maybe_unused]] BlockNum curr_block_num,
                                                     absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses) {
    absl::btree_set<Bytes> deleted_ts_prefixes{};
    // glee: parameter should be configured
    silkworm::lru_cache<evmc::address, std::optional<Account>> plainstate_accounts(100'000);

    trie::PrefixSet ret;
    db::Cursor plain_state(txn, db::table::kPlainState);

    for (auto const &[address, account] : buffer.accounts_diff()) {
        auto hashed_addresses_it{hashed_addresses.find(address)};
        if (hashed_addresses_it == hashed_addresses.end()) {
            const auto hashed_address{keccak256(address)};
            hashed_addresses_it = hashed_addresses.insert_or_assign(address, hashed_address).first;
        }

        std::optional<Account> plainstate_account{};
        if (auto item{plainstate_accounts.get(address)}; item != nullptr) {
            plainstate_account = *item;
        } else {
            auto ps_data{plain_state.find(db::to_slice(address.bytes), false)};
            if (ps_data && ps_data.value.length()) {
                auto [ps_acc, rlp_err]{Account::from_encoded_storage(db::from_slice(ps_data.value))};
                rlp::success_or_throw(rlp_err);
                plainstate_account.emplace(ps_acc);
            }
            plainstate_accounts.put(address, plainstate_account);
        }

        bool account_created{false};  // Whether the account has to be marked as created in changed list
        if (account.has_value()) {
            if (account->incarnation) {
                if (plainstate_account == std::nullopt ||
                    plainstate_account->incarnation != account->incarnation) {
                    (void)deleted_ts_prefixes.insert(
                        db::storage_prefix(address.bytes, account->incarnation));
                }
            }
        } else {
            account_created = true;
        }

        ret.insert(trie::unpack_nibbles(hashed_addresses_it->second.bytes), account_created);
    }

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

trie::PrefixSet MonadInterHashes::collect_storage_changes([[maybe_unused]] db::RWTxn& txn, db::MonadBuffer &buffer, BlockNum curr_block_num,
                                                     absl::btree_map<evmc::address, ethash_hash256>& hashed_addresses) {
    const Bytes starting_key{db::block_key(curr_block_num)};
    trie::PrefixSet ret;

    // Don't rehash same addresses
    absl::btree_map<evmc::address, ethash_hash256>::iterator hashed_addresses_it{hashed_addresses.begin()};

    for (const auto& [address, inc_loc_val] : buffer.storage_diff()) {
        hashed_addresses_it = hashed_addresses.find(address);
        if (hashed_addresses_it == hashed_addresses.end()) {
            const auto hashed_address{keccak256(address.bytes)};
            hashed_addresses_it = hashed_addresses.insert_or_assign(address, hashed_address).first;
        }

        Bytes hashed_key(db::kHashedStoragePrefixLength + (2 * kHashLength), '\0');
        std::memcpy(&hashed_key[0], hashed_addresses_it->second.bytes, kHashLength);
        for (const auto& [inc, loc_val] : inc_loc_val) {
            endian::store_big_u64(&hashed_key[kHashLength], inc);
            for (const auto& [loc, val] : loc_val) {
                const auto hashed_loc{keccak256(loc.bytes)};
                const auto unpacked_loc{trie::unpack_nibbles(hashed_loc.bytes)};
                std::memcpy(&hashed_key[db::kHashedStoragePrefixLength], unpacked_loc.data(), unpacked_loc.length());
                auto ret_item{ByteView(hashed_key.data(), db::kHashedStoragePrefixLength + unpacked_loc.length())};

                ret.insert(ret_item, val.length() == 0);
            }
        }
    }

    return ret;
}

StageResult MonadInterHashes::increment_intermediate_hashes(db::RWTxn& txn, db::MonadBuffer &buffer, BlockNum curr_block_num,
                                                       const evmc::bytes32* expected_root) {
    StageResult ret{StageResult::kSuccess};

    account_collector_ = std::make_unique<etl::Collector>(node_settings_);
    storage_collector_ = std::make_unique<etl::Collector>(node_settings_);

    // Cache of hashed addresses
    absl::btree_map<evmc::address, ethash_hash256> hashed_addresses{};
    // Collect all changes from changesets
    trie::PrefixSet account_changes{collect_account_changes(txn, buffer, curr_block_num, hashed_addresses)};
    trie::PrefixSet storage_changes{collect_storage_changes(txn, buffer, curr_block_num, hashed_addresses)};
    buffer.clear_diffs();
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

    db::Cursor target(txn, db::table::kTrieOfAccounts);
    MDBX_put_flags_t flags{target.empty() ? MDBX_put_flags_t::MDBX_APPEND : MDBX_put_flags_t::MDBX_UPSERT};
    account_collector_->load(target, nullptr, flags);

    target.bind(txn, db::table::kTrieOfStorage);
    flags = target.empty() ? MDBX_put_flags_t::MDBX_APPEND : MDBX_put_flags_t::MDBX_UPSERT;
    storage_collector_->load(target, nullptr, flags);
}

}  // namespace silkworm::stagedsync