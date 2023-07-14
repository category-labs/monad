#pragma once

#include "config.hpp"
#include <monad/core/assert.h>
#include <monad/db/config.hpp>
#include <test_resource_data.h>

#include <algorithm>
#include <chrono>
#include <filesystem>

#include <fmt/chrono.h>
#include <fmt/format.h>
#include <gtest/gtest.h>

MONAD_DB_NAMESPACE_BEGIN

struct InMemoryDB;
struct InMemoryTrieDB;
struct RocksDB;
struct RocksTrieDB;

MONAD_DB_NAMESPACE_END

MONAD_TEST_NAMESPACE_BEGIN

inline std::filesystem::path make_db_name(testing::TestInfo const &info)
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
             std::same_as<TDatabase, db::InMemoryTrieDB> ||
             std::same_as<TDatabase, db::RocksDB> ||
             std::same_as<TDatabase, db::RocksTrieDB>
inline TDatabase make_db()
{
    auto const *info = testing::UnitTest::GetInstance()->current_test_info();
    MONAD_ASSERT(info);
    if constexpr (
        std::same_as<TDatabase, db::InMemoryDB> ||
        std::same_as<TDatabase, db::InMemoryTrieDB>) {
        return TDatabase{};
    }
    else {
        return TDatabase{make_db_name(*info)};
    }
}

MONAD_TEST_NAMESPACE_END
