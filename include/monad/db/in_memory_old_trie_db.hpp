#pragma once

#include <monad/core/bytes_fmt.hpp>
#include <monad/core/int_fmt.hpp>
#include <monad/db/config.hpp>
#include <monad/db/db.hpp>
#include <monad/db/trie_db_process_changes.hpp>
#include <monad/db/trie_db_read_account.hpp>
#include <monad/db/trie_db_read_storage.hpp>
#include <monad/state2/state_deltas.hpp>
#include <monad/trie/in_memory_comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/trie.hpp>

#include <nlohmann/json.hpp>

MONAD_DB_NAMESPACE_BEGIN

// Database impl with trie root generating logic, backed by stl
struct InMemoryOldTrieDB : public Db
{
    template <typename Comparator>
    struct Trie
    {
        using cursor_t = trie::InMemoryCursor<Comparator>;
        using writer_t = trie::InMemoryWriter<Comparator>;
        using storage_t = typename cursor_t::storage_t;
        storage_t leaves_storage;
        cursor_t leaves_cursor;
        writer_t leaves_writer;
        storage_t trie_storage;
        cursor_t trie_cursor;
        writer_t trie_writer;
        trie::Trie<cursor_t, writer_t> trie;

        Trie()
            : leaves_storage{}
            , leaves_cursor{leaves_storage}
            , leaves_writer{leaves_storage}
            , trie_storage{}
            , trie_cursor{trie_storage}
            , trie_writer{trie_storage}
            , trie{leaves_cursor, trie_cursor, leaves_writer, trie_writer}
        {
        }

        [[nodiscard]] cursor_t make_leaf_cursor() const
        {
            return cursor_t{leaves_storage};
        }

        [[nodiscard]] cursor_t make_trie_cursor() const
        {
            return cursor_t{trie_storage};
        }
    };

    Trie<trie::InMemoryPathComparator> accounts_trie;
    Trie<trie::InMemoryPrefixPathComparator> storage_trie;
    std::unordered_map<bytes32_t, byte_string> code;

    ////////////////////////////////////////////////////////////////////
    // Db implementations
    ////////////////////////////////////////////////////////////////////

    [[nodiscard]] std::optional<Account>
    read_account(Address const &a) const override
    {
        return trie_db_read_account(
            a,
            accounts_trie.make_leaf_cursor(),
            accounts_trie.make_trie_cursor());
    }

    [[nodiscard]] bytes32_t
    read_storage(Address const &a, bytes32_t const &key) const override
    {
        return trie_db_read_storage(
            a,
            key,
            storage_trie.make_leaf_cursor(),
            storage_trie.make_trie_cursor());
    }

    [[nodiscard]] byte_string read_code(bytes32_t const &ch) const override
    {
        if (code.contains(ch)) {
            return code.at(ch);
        }
        return byte_string{};
    }

    void
    commit(StateDeltas const &state_deltas, Code const &code_delta) override
    {
        for (auto const &[ch, c] : code_delta) {
            code[ch] = c;
        }
        trie_db_process_changes(state_deltas, accounts_trie, storage_trie);

        accounts_trie.leaves_writer.write();
        accounts_trie.trie_writer.write();
        storage_trie.leaves_writer.write();
        storage_trie.trie_writer.write();
    }

    constexpr void
    create_and_prune_block_history(uint64_t /* block_number */) const override
    {
    }

    [[nodiscard]] bytes32_t state_root()
    {
        return accounts_trie.trie.root_hash();
    }

    [[nodiscard]] bytes32_t storage_root(Address const &a)
    {
        storage_trie.trie.set_trie_prefix(a);
        return storage_trie.trie.root_hash();
    }

    nlohmann::json to_json()
    {
        nlohmann::json state = nlohmann::json::object();
        auto const accounts = dump_accounts_from_db();
        auto const storage = dump_storage_from_db();

        state.update(accounts, /*merge_objects=*/true);
        state.update(storage, /*merge_objects=*/true);

        return state;
    }

private:
    template <typename THasBytes>
    [[nodiscard]] inline bytes32_t hash(THasBytes const &hashable)
    {
        return std::bit_cast<bytes32_t>(
            ethash::keccak256(hashable.bytes, sizeof(hashable.bytes)));
    }

    template <typename TCursor>
    void dump_accounts_from_trie(
        nlohmann::json &state, trie::Nibbles const &hashed_account_address,
        TCursor &leaf_cursor, TCursor &trie_cursor)
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

        auto const code = read_code(account.code_hash);
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

    void dump_accounts_from_db(
        nlohmann::json &state, Address address, Account const &account)
    {
        auto const keccaked_address_hex = fmt::format("{}", hash(address));

        state[keccaked_address_hex]["balance"] =
            fmt::format("{}", account.balance);

        state[keccaked_address_hex]["nonce"] =
            fmt::format("0x{:x}", account.nonce);

        auto const code = read_code(account.code_hash);
        state[keccaked_address_hex]["code"] = fmt::format(
            "0x{:02x}", fmt::join(std::as_bytes(std::span(code)), ""));
    }

    nlohmann::json dump_accounts_from_db()
    {
        nlohmann::json state = nlohmann::json::object();

        auto leaf_cursor = accounts_trie.make_leaf_cursor();
        auto trie_cursor = accounts_trie.make_trie_cursor();

        for (auto const &[address, _] : accounts_trie.leaves_storage) {
            auto const [hashed_account_address, size] =
                monad::trie::deserialize_nibbles(address);
            dump_accounts_from_trie(
                state, hashed_account_address, leaf_cursor, trie_cursor);
        }

        return state;
    }

    nlohmann::json dump_storage_from_db()
    {
        nlohmann::json state = nlohmann::json::object();
        auto leaf_cursor = storage_trie.make_leaf_cursor();
        auto trie_cursor = storage_trie.make_trie_cursor();

        for (auto const &[key, value] : storage_trie.leaves_storage) {
            monad::byte_string_view key_slice{key};
            dump_storage_from_trie(state, key_slice, leaf_cursor, trie_cursor);
        }
        return state;
    }
};

MONAD_DB_NAMESPACE_END
