#pragma once

#include <monad/db/concepts.hpp>
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

    using InMemoryDB = db::detail::InMemoryDB<Executor, db::ReadWrite>;
    using RocksDB = db::detail::RocksDB<Executor, db::ReadWrite>;
    using InMemoryTrieDB = db::detail::InMemoryTrieDB<Executor, db::ReadWrite>;
    using RocksTrieDB = db::detail::RocksTrieDB<Executor, db::ReadWrite>;
}

MONAD_TEST_NAMESPACE_END

MONAD_DB_NAMESPACE_BEGIN

template <>
[[nodiscard]] constexpr std::string_view
as_string<test::hijacked::RocksTrieDB>() noexcept
{
    return "hijackedrockstriedb";
}

template <>
[[nodiscard]] constexpr std::string_view
as_string<test::hijacked::RocksDB>() noexcept
{
    return "hijackedrocksdb";
}

MONAD_DB_NAMESPACE_END
