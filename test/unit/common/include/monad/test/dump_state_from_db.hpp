#pragma once

#include <monad/core/address.hpp>
#include <monad/core/address_fmt.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/bytes_fmt.hpp>
#include <monad/core/int.hpp>
#include <monad/core/int_fmt.hpp>
#include <monad/db/in_memory_old_trie_db.hpp>
#include <monad/db/trie_db_read_account.hpp>
#include <monad/test/config.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/nibbles_fmt.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

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
            fmt::format("{}", account.balance);

        state[keccaked_account_hex]["nonce"] =
            fmt::format("0x{:x}", account.nonce);

        auto const code = db.read_code(account.code_hash);
        state[keccaked_account_hex]["code"] = fmt::format(
            "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));

        state[keccaked_account_hex]["storage"] = nlohmann::json::object();
    }

    template <typename TCursor>
    void dump_storage_from_trie(
        nlohmann::json &state, byte_string_view key_slice, TCursor &leaf_cursor,
        TCursor &trie_cursor)
    {
        monad::Address account_address;
        std::memcpy(&account_address, key_slice.data(), sizeof(monad::Address));
        key_slice.remove_prefix(sizeof(monad::Address));

        auto const [keccaked_storage_key_nibbles, num_bytes] =
            monad::trie::deserialize_nibbles(key_slice);
        MONAD_ASSERT(num_bytes == key_slice.size());

        bytes32_t const storage_value =
            monad::trie_db_read_storage_with_hashed_key(
                account_address,
                keccaked_storage_key_nibbles,
                leaf_cursor,
                trie_cursor);
        auto const keccaked_account_address =
            fmt::format("{}", hash(account_address));
        state[keccaked_account_address]["original_account_address"] =
            fmt::format("{}", account_address);

        auto const storage_key =
            fmt::format("{}", keccaked_storage_key_nibbles);
        state[keccaked_account_address]["storage"][storage_key] =
            fmt::format("{}", storage_value);
    }

    template <typename TDatabase>
    void dump_accounts_from_db(
        TDatabase &db, nlohmann::json &state, Address address,
        Account const &account)
    {
        auto const keccaked_address_hex = fmt::format("{}", hash(address));

        state[keccaked_address_hex]["balance"] =
            fmt::format("{}", account.balance);

        state[keccaked_address_hex]["nonce"] =
            fmt::format("0x{:x}", account.nonce);

        auto const code = db.read_code(account.code_hash);
        state[keccaked_address_hex]["code"] = fmt::format(
            "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));
    }
}

[[nodiscard]] inline nlohmann::json
dump_accounts_from_db(monad::db::InMemoryOldTrieDB &db)
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
dump_storage_from_db(monad::db::InMemoryOldTrieDB &db)
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
