#pragma once

#include <monad/core/assert.h>
#include <monad/db/in_memory_db.hpp>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/db/rocks_db.hpp>
#include <monad/db/rocks_trie_db.hpp>
#include <monad/test/config.hpp>
#include <monad/test/hijacked_db.hpp>
#include <test_resource_data.h>

#include <algorithm>
#include <chrono>
#include <filesystem>

#include <quill/bundled/fmt/chrono.h>
#include <quill/bundled/fmt/format.h>

#include <gtest/gtest.h>

namespace fmt = fmtquill::v10;

MONAD_TEST_NAMESPACE_BEGIN

inline std::filesystem::path make_db_root(testing::TestInfo const &info)
{
    auto const test_suite_name = [&]() {
        std::string name = info.test_suite_name();
        std::ranges::replace(name, '/', '_');
        return name;
    }();

    auto const dir = monad::test_resource::build_dir / "rocksdb" /
                     test_suite_name / info.name();
    std::filesystem::create_directories(dir);
    return dir / fmt::format(
                     "{}", std::chrono::system_clock::now().time_since_epoch());
}

template <typename TDatabase>
    requires std::same_as<TDatabase, db::InMemoryDB> ||
             std::same_as<TDatabase, hijacked::InMemoryDB> ||
             std::same_as<TDatabase, db::InMemoryTrieDB> ||
             std::same_as<TDatabase, hijacked::InMemoryTrieDB> ||
             std::same_as<TDatabase, db::RocksDB> ||
             std::same_as<TDatabase, hijacked::RocksDB> ||
             std::same_as<TDatabase, db::RocksTrieDB> ||
             std::same_as<TDatabase, hijacked::RocksTrieDB>
inline TDatabase make_db()
{
    auto const *info = testing::UnitTest::GetInstance()->current_test_info();
    MONAD_ASSERT(info);
    if constexpr (
        std::same_as<TDatabase, db::InMemoryDB> ||
        std::same_as<TDatabase, hijacked::InMemoryDB> ||
        std::same_as<TDatabase, db::InMemoryTrieDB> ||
        std::same_as<TDatabase, hijacked::InMemoryTrieDB>) {
        return TDatabase{};
    }
    else {
        return TDatabase{make_db_root(*info), 0, 0};
    }
}

MONAD_TEST_NAMESPACE_END
