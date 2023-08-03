#pragma once

#include <monad/db/config.hpp>
#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

namespace hijacked
{
    struct Executor
    {
        static inline bool EXECUTED = false;
        [[nodiscard]] static constexpr auto execute(std::invocable auto &&f)
        {
            EXECUTED = true;
            return std::invoke(std::forward<decltype(f)>(f));
        }
    };

    using InMemoryDB = monad::db::detail::InMemoryDB<Executor>;
    using RocksDB = monad::db::detail::RocksDB<Executor>;
    using InMemoryTrieDB = monad::db::detail::InMemoryTrieDB<Executor>;
    using RocksTrieDB = monad::db::detail::RocksTrieDB<Executor>;
}

MONAD_TEST_NAMESPACE_END

MONAD_DB_NAMESPACE_BEGIN

template <>
[[nodiscard]] constexpr std::string_view
as_string<test::hijacked::RocksTrieDB>() noexcept
{
    return "hijackedrockstriedb";
}

MONAD_DB_NAMESPACE_END
