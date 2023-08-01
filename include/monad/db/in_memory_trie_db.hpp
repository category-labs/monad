#pragma once

#include <monad/db/trie_db_interface.hpp>
#include <monad/execution/execution_model.hpp>
#include <monad/trie/in_memory_comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/trie.hpp>

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    // Database impl with trie root generating logic, backed by stl
    template <typename TExecutor>
    struct InMemoryTrieDB
        : public TrieDBInterface<InMemoryTrieDB<TExecutor>, TExecutor>
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

        ////////////////////////////////////////////////////////////////////
        // DBInterface implementations
        ////////////////////////////////////////////////////////////////////
        constexpr void
        create_and_prune_block_history(uint64_t /* block_number */) const
        {
        }

        ////////////////////////////////////////////////////////////////////
        // TrieDBInterface implementations
        ////////////////////////////////////////////////////////////////////

        auto &accounts() { return accounts_trie; }
        auto &storage() { return storage_trie; }
        auto const &accounts() const { return accounts_trie; }
        auto const &storage() const { return storage_trie; }
    };
}

using InMemoryTrieDB =
    detail::InMemoryTrieDB<monad::execution::SerialExecution>;

MONAD_DB_NAMESPACE_END
