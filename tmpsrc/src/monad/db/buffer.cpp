#include <monad/db/buffer.hpp>

#include <algorithm>
#include <iostream>

#include <absl/container/btree_set.h>

#include <silkworm/common/endian.hpp>
#include <silkworm/db/access_layer.hpp>
#include <silkworm/db/tables.hpp>
#include <silkworm/types/log_cbor.hpp>
#include <silkworm/types/receipt_cbor.hpp>

namespace silkworm::db {

void MonadBuffer::begin_block(uint64_t block_number) {
    block_number_ = block_number;
    changed_storage_.clear();
}

void MonadBuffer::update_account(const evmc::address& address, std::optional<Account> initial,
                            std::optional<Account> current) {
    const bool equal{current == initial};
    const bool account_deleted{!current.has_value()};

    if (equal && !account_deleted && !changed_storage_.contains(address)) {
        // Follows the Erigon logic when to populate account changes.
        // See (ChangeSetWriter)UpdateAccountData & DeleteAccount.
        return;
    }

    
    silkworm::Bytes encoded_initial{};
    if (initial) {
        bool omit_code_hash{!account_deleted};
        encoded_initial = initial->encode_for_storage(omit_code_hash);
    }

    block_account_changes_[block_number_].insert_or_assign(address, encoded_initial);

    auto diff_it{accounts_diff_.find(address)};
    if (diff_it == accounts_diff_.end()) {
        accounts_diff_.insert_or_assign(address, initial);
    }

    if (equal) {
        return;
    }
    auto it{accounts_.find(address)};
    if (it != accounts_.end()) {
        it->second = current;
    } else {
        accounts_[address] = current;
    }

    if (account_deleted && initial->incarnation) {
        incarnations_.insert_or_assign(address, initial->incarnation);
    }
}

void MonadBuffer::update_account_code(const evmc::address& address, uint64_t incarnation, const evmc::bytes32& code_hash,
                                 silkworm::ByteView code) {
    // Don't overwrite already existing code so that views of it
    // that were previously returned by read_code() are still valid.
    hash_to_code_.try_emplace(code_hash, code);

    storage_prefix_to_code_hash_.insert_or_assign(silkworm::db::storage_prefix(address, incarnation), code_hash);
}

void MonadBuffer::update_storage(const evmc::address& address, uint64_t incarnation, const evmc::bytes32& location,
                            const evmc::bytes32& initial, const evmc::bytes32& current) {
    if (current == initial) {
        return;
    }
    
    changed_storage_.insert(address);
    silkworm::ByteView initial_val{silkworm::zeroless_view(initial)};
    if (block_storage_changes_[block_number_][address][incarnation]
            .insert_or_assign(location, initial_val)
            .second) {
    }

    auto it{storage_diff_[address][incarnation].find(location)};
    if (it == storage_diff_[address][incarnation].end()) {
        storage_diff_[address][incarnation].insert_or_assign(location, initial_val);
    }

    storage_[address][incarnation].insert_or_assign(location, current);
}

void MonadBuffer::write_history_to_db() {
    if (!block_account_changes_.empty()) {
        auto account_change_table{silkworm::db::open_cursor(txn_, silkworm::db::table::kAccountChangeSet)};
        silkworm::Bytes change_key(sizeof(silkworm::BlockNum), '\0');
        silkworm::Bytes change_value(silkworm::kAddressLength + 128 /* see comment*/,
                           '\0');  // Max size of encoded value is 85. We allocate - once - some byte more for safety
                                   // and avoid reallocation or resizing in the loop
        for (const auto& [block_num, account_changes] : block_account_changes_) {
            silkworm::endian::store_big_u64(change_key.data(), block_num);
            for (const auto& [address, account_encoded] : account_changes) {
                std::memcpy(&change_value[0], address.bytes, kAddressLength);
                std::memcpy(&change_value[kAddressLength], account_encoded.data(), account_encoded.length());
                mdbx::slice k{to_slice(change_key)};
                mdbx::slice v{change_value.data(), kAddressLength + account_encoded.length()};
                mdbx::error::success_or_throw(account_change_table.put(k, &v, MDBX_APPENDDUP));
            }
        }
        block_account_changes_.clear();
    }

    if (!block_storage_changes_.empty()) {
        Bytes change_key(sizeof(BlockNum) + kPlainStoragePrefixLength, '\0');
        Bytes change_value(kHashLength + 128, '\0');  // Se comment above (account changes) for explanation about 128

        auto storage_change_table{db::open_cursor(txn_, table::kStorageChangeSet)};
        for (const auto& [block_num, storage_changes] : block_storage_changes_) {
            endian::store_big_u64(&change_key[0], block_num);
            for (const auto& [address, incarnations_locations_values] : storage_changes) {
                std::memcpy(&change_key[sizeof(BlockNum)], address.bytes, kAddressLength);
                for (const auto& [incarnation, locations_values] : incarnations_locations_values) {
                    endian::store_big_u64(&change_key[sizeof(BlockNum) + kAddressLength], incarnation);
                    for (const auto& [location, value] : locations_values) {
                        std::memcpy(&change_value[0], location.bytes, kHashLength);
                        std::memcpy(&change_value[kHashLength], value.data(), value.length());
                        mdbx::slice change_value_slice{change_value.data(), kHashLength + value.length()};
                        mdbx::error::success_or_throw(
                            storage_change_table.put(to_slice(change_key), &change_value_slice, MDBX_APPENDDUP));
                    }
                }
            }
        }
        block_storage_changes_.clear();
    }

    if (!receipts_.empty()) {
        auto receipt_table{db::open_cursor(txn_, table::kBlockReceipts)};
        for (const auto& [block_key, receipts] : receipts_) {
            auto k{to_slice(block_key)};
            auto v{to_slice(receipts)};
            mdbx::error::success_or_throw(receipt_table.put(k, &v, MDBX_APPEND));
        }
        receipts_.clear();
    }

    if (!logs_.empty()) {
        auto log_table{db::open_cursor(txn_, table::kLogs)};
        for (const auto& [log_key, value] : logs_) {
            auto k{to_slice(log_key)};
            auto v{to_slice(value)};
            mdbx::error::success_or_throw(log_table.put(k, &v, MDBX_APPEND));
        }
        logs_.clear();
    }
}

void MonadBuffer::write_state_to_db() {
    /*
     * ENSURE PlainState updates are Last !!!
     * Also ensure to clear unneeded memory data ASAP to let the OS cache
     * to store more database pages for longer
     */

    if (!incarnations_.empty()) {
        auto incarnation_table{db::open_cursor(txn_, table::kIncarnationMap)};
        Bytes data(kIncarnationLength, '\0');
        for (const auto& [address, incarnation] : incarnations_) {
            endian::store_big_u64(&data[0], incarnation);
            incarnation_table.upsert(to_slice(address), to_slice(data));
        }
        incarnations_.clear();
    }

    if (!hash_to_code_.empty()) {
        auto code_table{db::open_cursor(txn_, table::kCode)};
        for (const auto& entry : hash_to_code_) {
            code_table.upsert(to_slice(entry.first), to_slice(entry.second));
        }
        hash_to_code_.clear();
    }

    if (!storage_prefix_to_code_hash_.empty()) {
        auto code_hash_table{db::open_cursor(txn_, table::kPlainCodeHash)};
        for (const auto& entry : storage_prefix_to_code_hash_) {
            code_hash_table.upsert(to_slice(entry.first), to_slice(entry.second));
        }
        storage_prefix_to_code_hash_.clear();
    }

    // Extract sorted index of unique addresses before inserting into the DB
    absl::btree_set<evmc::address> addresses;
    for (auto& x : accounts_) {
        addresses.insert(x.first);
    }
    for (auto& x : storage_) {
        addresses.insert(x.first);
    }

    auto state_table{db::open_cursor(txn_, table::kPlainState)};
    for (const auto& address : addresses) {
        if (auto it{accounts_.find(address)}; it != accounts_.end()) {
            auto key{to_slice(address)};
            state_table.erase(key, /*whole_multivalue=*/true);  // PlainState is multivalue
            if (it->second.has_value()) {
                Bytes encoded{it->second->encode_for_storage()};
                state_table.upsert(key, to_slice(encoded));
            }
            // accounts_.erase(it);
        }

        if (auto it{storage_.find(address)}; it != storage_.end()) {
            for (const auto& [incarnation, contract_storage] : it->second) {
                Bytes prefix{storage_prefix(address, incarnation)};
                for (const auto& [location, value] : contract_storage) {
                    upsert_storage_value(state_table, prefix, location, value);
                }
            }
            // storage_.erase(it);
        }
    }
}

void MonadBuffer::write_hash_to_db(){
    // tzhi: migrate hashstate::hash_from_account_changeset()
    ChangedAddresses changed_addresses{};
    for(auto const& [address, account]: accounts_diff_){
        auto address_hash = to_bytes32(keccak256(address).bytes);
        auto encoded_account = Bytes();
        if(accounts_[address].has_value()){
            encoded_account = accounts_[address]->encode_for_storage(false);
        }
        changed_addresses[address] = std::make_pair(address_hash, encoded_account);
    }
    
    // tzhi: might be wrong but I don't think we can get rid of any db access here
    auto source_plaincode{db::open_cursor(txn_, db::table::kPlainCodeHash)};
    auto target_hashed_accounts{db::open_cursor(txn_, db::table::kHashedAccounts)};
    auto target_hashed_code{db::open_cursor(txn_, db::table::kHashedCodeHash)};

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

    // tzhi: migrate HashState::hash_from_storage_changeset()
    db::StorageChanges storage_changes{};
    absl::btree_map<evmc::address, evmc::bytes32> hashed_addresses{};

    for(auto const& [address, inc_loc_val]: storage_diff_){
        for(auto const& [inc, loc_val]: inc_loc_val){
            if(!hashed_addresses.contains(address)){
                hashed_addresses[address] = to_bytes32(keccak256(address.bytes).bytes);
                storage_changes[address].insert_or_assign(inc, absl::btree_map<evmc::bytes32, Bytes>());
            }

            Bytes plain_storage_prefix{db::storage_prefix(address, inc)};
            for(auto const& [loc, val]: loc_val){
                if (!storage_changes[address][inc].contains(loc)) {
                    auto encoded_storage = Bytes();
                    if(storage_[address][inc].contains(loc)){
                        encoded_storage = silkworm::zeroless_view(storage_[address][inc][loc]);
                    }
                    storage_changes[address][inc].insert_or_assign(loc, encoded_storage);
                }
            }
        }
    }
    // tzhi: again, don't think this part could be further simplified
    auto target_hashed_storage{db::open_cursor(txn_, db::table::kHashedStorage)};

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

    accounts_.clear();
    storage_.clear();
}

void MonadBuffer::write_to_db() {
    write_history_to_db();

    // This should be very last to be written so updated pages
    // have higher chances not to be evicted from RAM
    write_state_to_db();

    write_hash_to_db();
}

// Erigon WriteReceipts in core/rawdb/accessors_chain.go
void MonadBuffer::insert_receipts(uint64_t block_number, const std::vector<silkworm::Receipt>& receipts) {
    for (uint32_t i{0}; i < receipts.size(); ++i) {
        if (receipts[i].logs.empty()) {
            continue;
        }

        silkworm::Bytes key{silkworm::db::log_key(block_number, i)};
        silkworm::Bytes value{silkworm::cbor_encode(receipts[i].logs)};

        logs_.insert_or_assign(key, value);
    }

    silkworm::Bytes key{silkworm::db::block_key(block_number)};
    silkworm::Bytes value{silkworm::cbor_encode(receipts)};
    receipts_[key] = value;
}

evmc::bytes32 MonadBuffer::state_root_hash() const {
    throw std::runtime_error(std::string(__FUNCTION__).append(" not yet implemented"));
}

uint64_t MonadBuffer::current_canonical_block() const {
    throw std::runtime_error(std::string(__FUNCTION__).append(" not yet implemented"));
}

std::optional<evmc::bytes32> MonadBuffer::canonical_hash(uint64_t) const {
    throw std::runtime_error(std::string(__FUNCTION__).append(" not yet implemented"));
}

void MonadBuffer::canonize_block(uint64_t, const evmc::bytes32&) {
    throw std::runtime_error(std::string(__FUNCTION__).append(" not yet implemented"));
}

void MonadBuffer::decanonize_block(uint64_t) {
    throw std::runtime_error(std::string(__FUNCTION__).append(" not yet implemented"));
}

void MonadBuffer::insert_block(const silkworm::Block& block, const evmc::bytes32& hash) {
    uint64_t block_number{block.header.number};
    silkworm::Bytes key{silkworm::db::block_key(block_number, hash.bytes)};
    headers_[key] = block.header;
    bodies_[key] = block;

    if (block_number == 0) {
        difficulty_[key] = 0;
    } else {
        std::optional<intx::uint256> parent_difficulty{total_difficulty(block_number - 1, block.header.parent_hash)};
        difficulty_[key] = parent_difficulty.value_or(0);
    }
    difficulty_[key] += block.header.difficulty;
}

std::optional<intx::uint256> MonadBuffer::total_difficulty(uint64_t block_number,
                                                      const evmc::bytes32& block_hash) const noexcept {
    silkworm::Bytes key{silkworm::db::block_key(block_number, block_hash.bytes)};
    if (auto it{difficulty_.find(key)}; it != difficulty_.end()) {
        return it->second;
    }
    return silkworm::db::read_total_difficulty(txn_, key);
}

std::optional<silkworm::BlockHeader> MonadBuffer::read_header(uint64_t block_number, const evmc::bytes32& block_hash) const noexcept {
    silkworm::Bytes key{silkworm::db::block_key(block_number, block_hash.bytes)};
    if (auto it{headers_.find(key)}; it != headers_.end()) {
        return it->second;
    }
    silkworm::Block block;  // TODO just read header
    if (!silkworm::db::read_block_by_number(block_db_, block_number, false, block)) {
        return std::nullopt;
    }
    return block.header;
}

bool MonadBuffer::read_body(uint64_t block_number, const evmc::bytes32& block_hash, silkworm::BlockBody& body) const noexcept {
    silkworm::Bytes key{silkworm::db::block_key(block_number, block_hash.bytes)};
    if (auto it{bodies_.find(key)}; it != bodies_.end()) {
        body = it->second;
        return true;
    }
    silkworm::Block block;
    if (!silkworm::db::read_block_by_number(block_db_, block_number, false, block)) {
        return false;
    }
    body = block;
    return true;
}

std::optional<Account> MonadBuffer::read_account(const evmc::address& address) const noexcept {
    if (auto it{accounts_.find(address)}; it != accounts_.end()) {
        return it->second;
    }
    auto db_account{silkworm::db::read_account(txn_, address, historical_block_)};
    accounts_[address] = db_account;
    return db_account;
}

silkworm::ByteView MonadBuffer::read_code(const evmc::bytes32& code_hash) const noexcept {
    if (auto it{hash_to_code_.find(code_hash)}; it != hash_to_code_.end()) {
        return it->second;
    }
    std::optional<silkworm::ByteView> code{silkworm::db::read_code(txn_, code_hash)};
    if (code.has_value()) {
        return *code;
    } else {
        return {};
    }
}

evmc::bytes32 MonadBuffer::read_storage(const evmc::address& address, uint64_t incarnation,
                                   const evmc::bytes32& location) const noexcept {
    if (auto it1{storage_.find(address)}; it1 != storage_.end()) {
        if (auto it2{it1->second.find(incarnation)}; it2 != it1->second.end()) {
            if (auto it3{it2->second.find(location)}; it3 != it2->second.end()) {
                return it3->second;
            }
        }
    }
    auto db_storage{silkworm::db::read_storage(txn_, address, incarnation, location, historical_block_)};
    storage_[address][incarnation][location] = db_storage;
    return db_storage;
}

uint64_t MonadBuffer::previous_incarnation(const evmc::address& address) const noexcept {
    if (auto it{incarnations_.find(address)}; it != incarnations_.end()) {
        return it->second;
    }
    std::optional<uint64_t> incarnation{silkworm::db::read_previous_incarnation(txn_, address, historical_block_)};
    return incarnation.value_or(0);
}

void MonadBuffer::unwind_state_changes(uint64_t) {
    throw std::runtime_error(std::string(__FUNCTION__).append(" not yet implemented"));
}

}  // namespace monad