#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/logging/formatter.hpp>
#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

namespace detail
{
    template <typename THasBytes>
    [[nodiscard]] inline bytes32_t hash(THasBytes const &hashable)
    {
        return std::bit_cast<bytes32_t>(
            ethash::keccak256(hashable.bytes, sizeof(hashable.bytes)));
    }

    template <typename TDatabase, typename TCursor>
    void dump_accounts_from_trie(
        nlohmann::json &state, TDatabase const &db,
        trie::Nibbles const &hashed_account_address, TCursor &leaf_cursor,
        TCursor &trie_cursor)
    {
        auto const maybe_account = monad::trie_db_read_account(
            hashed_account_address, leaf_cursor, trie_cursor);

        MONAD_ASSERT(maybe_account.has_value());
        auto const &account = maybe_account.value();

        auto const keccaked_account_hex =
            fmt::format("{}", hashed_account_address);

        state[keccaked_account_hex]["balance"] =
            "0x" + intx::to_string(account.balance, 16);

        state[keccaked_account_hex]["nonce"] =
            fmt::format("0x{:x}", account.nonce);

        auto const code = db.read_code(account.code_hash);
        state[keccaked_account_hex]["code"] = "0x" + evmc::hex(code);
    }

    template <typename TCursor>
    void dump_storage_from_trie(
        nlohmann::json &state, byte_string_view key_slice, TCursor &leaf_cursor,
        TCursor &trie_cursor)
    {
        monad::address_t account_address;
        std::memcpy(
            &account_address, key_slice.data(), sizeof(monad::address_t));
        key_slice.remove_prefix(sizeof(monad::address_t));

        auto const [keccaked_storage_key_nibbles, num_bytes] =
            monad::trie::deserialize_nibbles(key_slice);
        MONAD_ASSERT(num_bytes == key_slice.size());

        bytes32_t const storage_value =
            monad::trie_db_read_storage_with_hashed_key(
                account_address,
                0u,
                keccaked_storage_key_nibbles,
                leaf_cursor,
                trie_cursor);
        auto const keccaked_account_address =
            fmt::format("{}", hash(account_address));
        state[keccaked_account_address]["storage"]["original_account_address"] =
            fmt::format("{}", account_address);

        auto const storage_key =
            fmt::format("{}", keccaked_storage_key_nibbles);
        state[keccaked_account_address]["storage"][storage_key] =
            fmt::format("{}", storage_value);
    }

    template <typename TDatabase>
    void dump_accounts_from_db(
        TDatabase &db, nlohmann::json &state, address_t address,
        Account const &account)
    {
        auto const keccaked_address_hex = fmt::format("{}", hash(address));

        state[keccaked_address_hex]["balance"] =
            "0x" + intx::to_string(account.balance, 16);

        state[keccaked_address_hex]["nonce"] =
            fmt::format("0x{:x}", account.nonce);

        auto const code = db.read_code(account.code_hash);
        state[keccaked_address_hex]["code"] = "0x" + evmc::hex(code);
    }
}

[[nodiscard]] inline nlohmann::json
dump_accounts_from_db(monad::db::RocksTrieDB &db)
{
    nlohmann::json state = nlohmann::json::object();

    auto leaf_cursor = db.accounts_trie.make_leaf_cursor();
    auto trie_cursor = db.accounts_trie.make_trie_cursor();

    std::unique_ptr<rocksdb::Iterator> it{
        db.db->NewIterator({}, db.accounts_trie.leaves_cursor.cf_)};

    for (it->SeekToFirst(); it->Valid(); it->Next()) {
        auto const hashed_account_address =
            monad::trie::deserialize_nibbles(it->key());
        detail::dump_accounts_from_trie(
            state, db, hashed_account_address, leaf_cursor, trie_cursor);
    }

    return state;
}

[[nodiscard]] inline nlohmann::json
dump_storage_from_db(monad::db::RocksTrieDB &db)
{
    nlohmann::json state = nlohmann::json::object();
    auto leaf_cursor = db.storage_trie.make_leaf_cursor();
    auto trie_cursor = db.storage_trie.make_trie_cursor();

    std::unique_ptr<rocksdb::Iterator> it{
        db.db->NewIterator({}, db.storage_trie.leaves_cursor.cf_)};

    for (it->SeekToFirst(); it->Valid(); it->Next()) {
        auto key_slice = monad::db::from_slice(it->key());
        detail::dump_storage_from_trie(
            state, key_slice, leaf_cursor, trie_cursor);
    }
    return state;
}

[[nodiscard]] inline nlohmann::json
dump_accounts_from_db(monad::db::RocksDB &db)
{
    nlohmann::json state = nlohmann::json::object();
    std::unique_ptr<rocksdb::Iterator> it{
        db.db->NewIterator({}, db.accounts_cf())};
    for (it->SeekToFirst(); it->Valid(); it->Next()) {
        auto const key_view = monad::db::from_slice(it->key());

        address_t address;
        std::memcpy(&address, key_view.data(), sizeof(address_t));

        auto const value = monad::db::from_slice(it->value());

        Account account;
        bytes32_t storage_root;
        rlp::decode_account(account, storage_root, value);

        detail::dump_accounts_from_db(db, state, address, account);
    }
    return state;
}
[[nodiscard]] inline nlohmann::json dump_storage_from_db(monad::db::RocksDB &db)
{
    nlohmann::json state = nlohmann::json::object();
    std::unique_ptr<rocksdb::Iterator> it{
        db.db->NewIterator({}, db.storage_cf())};

    for (it->SeekToFirst(); it->Valid(); it->Next()) {
        auto const key_slice = db::from_slice(it->key());
        byte_string_view key_view{key_slice};
        MONAD_ASSERT(key_view.size() == sizeof(address_t) + sizeof(bytes32_t));

        monad::address_t address;
        std::copy_n(key_view.data(), sizeof(address_t), address.bytes);
        auto const keccaked_account_hex =
            fmt::format("{}", detail::hash(address));
        key_view.remove_prefix(sizeof(address_t));

        bytes32_t storage_address;
        std::copy_n(key_view.data(), sizeof(bytes32_t), storage_address.bytes);

        bytes32_t keccaked_storage_key = detail::hash(storage_address);

        auto const value_slice = db::from_slice(it->value());

        bytes32_t storage_value;
        std::copy_n(value_slice.data(), sizeof(bytes32_t), storage_value.bytes);

        state[keccaked_account_hex]["storage"]["original_account_address"] =
            fmt::format("{}", address);
        state[keccaked_account_hex]["storage"]
             [fmt::format("{}", keccaked_storage_key)] =
                 fmt::format("{}", storage_value);
    }

    return state;
}

[[nodiscard]] inline nlohmann::json
dump_accounts_from_db(monad::db::InMemoryTrieDB &db)
{
    nlohmann::json state = nlohmann::json::object();

    auto leaf_cursor = db.accounts_trie.make_leaf_cursor();
    auto trie_cursor = db.accounts_trie.make_trie_cursor();

    for (auto const &[address, _] : db.accounts_trie.leaves_storage) {
        auto const [hashed_account_address, size] =
            monad::trie::deserialize_nibbles(address);
        detail::dump_accounts_from_trie(
            state, db, hashed_account_address, leaf_cursor, trie_cursor);
    }

    return state;
}

[[nodiscard]] inline nlohmann::json
dump_storage_from_db(monad::db::InMemoryTrieDB &db)
{
    nlohmann::json state = nlohmann::json::object();
    auto leaf_cursor = db.storage_trie.make_leaf_cursor();
    auto trie_cursor = db.storage_trie.make_trie_cursor();

    for (auto const &[key, value] : db.storage_trie.leaves_storage) {
        monad::byte_string_view key_slice{key};
        detail::dump_storage_from_trie(
            state, key_slice, leaf_cursor, trie_cursor);
    }
    return state;
}

template <typename TDatabase>
nlohmann::json dump_state_from_db(TDatabase &db)
{
    nlohmann::json state = nlohmann::json::object();
    auto const accounts = dump_accounts_from_db(db);
    auto const storage = dump_storage_from_db(db);

    state.update(accounts, /*merge_objects=*/true);
    state.update(storage, /*merge_objects=*/true);

    return state;
}

MONAD_TEST_NAMESPACE_END
