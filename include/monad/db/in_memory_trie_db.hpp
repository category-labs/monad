#pragma once

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

MONAD_DB_NAMESPACE_BEGIN

// Database impl with trie root generating logic, backed by stl
struct InMemoryTrieDB : public Db
{
    template <typename TComparator>
    struct Trie
    {
        using cursor_t = trie::InMemoryCursor<TComparator>;
        using writer_t = trie::InMemoryWriter<TComparator>;
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
    read_account(address_t const &a) const override
    {
        return trie_db_read_account(
            a,
            accounts_trie.make_leaf_cursor(),
            accounts_trie.make_trie_cursor());
    }

    [[nodiscard]] bytes32_t
    read_storage(address_t const &a, bytes32_t const &key) const override
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

    [[nodiscard]] bytes32_t storage_root(address_t const &a)
    {
        storage_trie.trie.set_trie_prefix(a);
        return storage_trie.trie.root_hash();
    }
};

MONAD_DB_NAMESPACE_END
