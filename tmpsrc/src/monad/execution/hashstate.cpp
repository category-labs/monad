#include <monad/execution/hashstate.hpp>

#include <silkworm/common/endian.hpp>
#include <silkworm/common/log.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/db/util.hpp>
#include <silkworm/etl/collector.hpp>

namespace silkworm::stagedsync {

StageResult MonadHashState::forward(db::RWTxn& txn) {
    auto block_num{db::stages::read_stage_progress(*txn, db::stages::kHashStateKey) + 1};
    assert(block_num == db::stages::read_stage_progress(*txn, db::stages::kExecutionKey));
    success_or_throw(hash_from_account_changeset(txn, block_num));
    success_or_throw(hash_from_storage_changeset(txn, block_num));
    db::stages::write_stage_progress(*txn, db::stages::kHashStateKey, block_num);
    txn.commit();

    return StageResult::kSuccess;
}

StageResult MonadHashState::hash_from_account_changeset(db::RWTxn& txn, BlockNum curr_block_num) {
    /*
     * 1) Read AccountChangeSet from previous_progress to 'to'
     * 2) For each address changed hash it and lookup current value from PlainState
     * 3) Process the collected list and write values into Hashed tables (Account and Code)
     */

    ChangedAddresses changed_addresses{};

    auto source_initial_key{db::block_key(curr_block_num)};
    auto source_changeset{db::open_cursor(*txn, db::table::kAccountChangeSet)};
    auto source_plainstate{db::open_cursor(*txn, db::table::kPlainState)};
    auto changeset_data{source_changeset.find(db::to_slice(source_initial_key), /*throw_notfound=*/false)};

    while (changeset_data) {
        auto changeset_value_view{db::from_slice(changeset_data.value)};
        evmc::address address{to_evmc_address(changeset_value_view)};
        if (!changed_addresses.contains(address)) {
            auto address_hash{to_bytes32(keccak256(address.bytes).bytes)};
            auto plainstate_data{source_plainstate.find(db::to_slice(address.bytes), /*throw_notfound=*/false)};
            if (plainstate_data.done) {
                Bytes current_value{db::from_slice(plainstate_data.value)};
                changed_addresses[address] = std::make_pair(address_hash, current_value);
            } else {
                changed_addresses[address] = std::make_pair(address_hash, Bytes());
            }
        }
        changeset_data = source_changeset.to_current_next_multi(/*throw_notfound=*/false);
    }
        
    source_changeset.close();
    source_plainstate.close();
    return write_changes_from_changed_addresses(txn, changed_addresses);
}

StageResult MonadHashState::hash_from_storage_changeset(db::RWTxn& txn, BlockNum curr_block_num) {
    /*
     * 1) Read StorageChangeSet from previous_progress to 'to'
     * 2) For each address + incarnation changed hash it and lookup current value from PlainState
     * 3) Process the collected list and write values into HashedStorage
     */
    
    db::StorageChanges storage_changes{};
    absl::btree_map<evmc::address, evmc::bytes32> hashed_addresses{};

    auto source_changeset{db::open_cursor(*txn, db::table::kStorageChangeSet)};
    auto source_plainstate{db::open_cursor(*txn, db::table::kPlainState)};

    auto source_initial_key{db::block_key(curr_block_num)};
    auto changeset_data{source_changeset.lower_bound(db::to_slice(source_initial_key), /*throw_notfound=*/false)};

    // tzhi: we can't remove this nested loop for now
    // because although the block number is fixed, the key also contains address, which is not fixed
    while (changeset_data.done) {
        auto changeset_key_view{db::from_slice(changeset_data.key)};

        changeset_key_view.remove_prefix(8);
        evmc::address address{to_evmc_address(changeset_key_view)};
        changeset_key_view.remove_prefix(kAddressLength);

        const auto incarnation{endian::load_big_u64(changeset_key_view.data())};
        if (!incarnation) {
            throw StageError(StageResult::kUnexpectedError, "Unexpected EOA in StorageChangeset");
        }
        if (!hashed_addresses.contains(address)) {
            hashed_addresses[address] = to_bytes32(keccak256(address.bytes).bytes);
            storage_changes[address].insert_or_assign(incarnation, absl::btree_map<evmc::bytes32, Bytes>());
        }

        Bytes plain_storage_prefix{db::storage_prefix(address, incarnation)};

        while (changeset_data.done) {
            auto changeset_value_view{db::from_slice(changeset_data.value)};
            auto location{to_bytes32(changeset_value_view)};
            if (!storage_changes[address][incarnation].contains(location)) {
                auto plain_state_value{db::find_value_suffix(source_plainstate, plain_storage_prefix, location)};
                storage_changes[address][incarnation].insert_or_assign(location,
                                                                        plain_state_value.value_or(Bytes()));
            }
            changeset_data = source_changeset.to_current_next_multi(/*throw_notfound=*/false);
        }
        changeset_data = source_changeset.to_next(/*throw_notfound=*/false);
    }

    return write_changes_from_changed_storage(txn, storage_changes, hashed_addresses);
}

StageResult MonadHashState::write_changes_from_changed_addresses(db::RWTxn& txn, const ChangedAddresses& changed_addresses) {
    auto source_plaincode{db::open_cursor(*txn, db::table::kPlainCodeHash)};
    auto target_hashed_accounts{db::open_cursor(*txn, db::table::kHashedAccounts)};
    auto target_hashed_code{db::open_cursor(*txn, db::table::kHashedCodeHash)};

    Bytes plain_code_key(kAddressLength + db::kIncarnationLength, '\0');  // Only one allocation
    Bytes hashed_code_key(kHashLength + db::kIncarnationLength, '\0');    // Only one allocation

    for (const auto& [address, pair] : changed_addresses) {
        auto& [address_hash, current_encoded_value] = pair;
        if (!current_encoded_value.empty()) {
            // Update HashedAccounts table
            target_hashed_accounts.upsert(db::to_slice(address_hash.bytes), db::to_slice(current_encoded_value));

            // Lookup value in PlainCodeHash for Contract
            auto [incarnation, err]{Account::incarnation_from_encoded_storage(current_encoded_value)};
            rlp::success_or_throw(err);
            if (incarnation) {
                std::memcpy(&plain_code_key[0], address.bytes, kAddressLength);
                std::memcpy(&hashed_code_key[0], address_hash.bytes, kHashLength);
                endian::store_big_u64(&hashed_code_key[kHashLength], incarnation);
                endian::store_big_u64(&plain_code_key[kAddressLength], incarnation);
                auto code_data{source_plaincode.find(db::to_slice(plain_code_key),
                                                     /*throw_notfound=*/false)};
                if (code_data.done && !code_data.value.empty()) {
                    target_hashed_code.upsert(db::to_slice(hashed_code_key), code_data.value);
                } else {
                    (void)target_hashed_code.erase(db::to_slice(hashed_code_key));
                }
            }
        } else {
            (void)target_hashed_accounts.erase(db::to_slice(address_hash.bytes));
        }
    }

    return StageResult::kSuccess;
}

StageResult MonadHashState::write_changes_from_changed_storage(
    db::RWTxn& txn, db::StorageChanges& storage_changes,
    const absl::btree_map<evmc::address, evmc::bytes32>& hashed_addresses) {
    auto target_hashed_storage{db::open_cursor(*txn, db::table::kHashedStorage)};

    evmc::address last_address{};
    Bytes hashed_storage_prefix(db::kHashedStoragePrefixLength, '\0');  // One allocation only
    for (const auto& [address, data] : storage_changes) {
        if (address != last_address) {
            last_address = address;
            std::memcpy(&hashed_storage_prefix[0], hashed_addresses.at(last_address).bytes, kHashLength);
        }

        for (const auto& [incarnation, data1] : data) {
            endian::store_big_u64(&hashed_storage_prefix[kHashLength], incarnation);
            for (const auto& [location, value] : data1) {
                auto hashed_location{keccak256(location.bytes)};
                db::upsert_storage_value(target_hashed_storage, hashed_storage_prefix, hashed_location.bytes, value);
            }
        }
    }

    return StageResult::kSuccess;
}

// glee: removed in next commit
std::vector<std::string> MonadHashState::get_log_progress() { return {}; }

}  // namespace silkworm::stagedsync