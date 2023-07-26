#pragma once

#include <monad/db/config.hpp>
#include <monad/db/util.hpp>
#include <monad/execution/config.hpp>

#include <fmt/format.h>
#include <tl/expected.hpp>

#include <concepts>
#include <filesystem>

MONAD_EXECUTION_NAMESPACE_BEGIN
struct BoostFiberExecution;
MONAD_EXECUTION_NAMESPACE_END

MONAD_DB_NAMESPACE_BEGIN

namespace detail
{
    template <typename TExecution>
    struct RocksTrieDB;
};
using RocksTrieDB = detail::RocksTrieDB<monad::execution::BoostFiberExecution>;

// Preparing initial db state and return the path for opening. If preparation
// fails, return a string explanation
template <typename TDB>
    requires std::same_as<TDB, db::RocksTrieDB>
[[nodiscard]] inline tl::expected<std::filesystem::path, std::string>
prepare_state(TDB const &db, uint64_t block_number)
{
    namespace fs = std::filesystem;

    auto const current_dir = db.root / "CURRENT";

    // overwrite CURRENT if exists
    if (fs::exists(current_dir)) {
        fs::remove_all(current_dir);
    }

    fs::create_directories(current_dir);

    auto const path = current_dir / monad::db::as_string<TDB>();

    if (block_number) {
        auto const starting_block = db.root / std::to_string(block_number - 1);

        if (!fs::exists(starting_block)) {
            return tl::make_unexpected(fmt::format(
                "{} starting block directory is missing {}",
                __PRETTY_FUNCTION__,
                starting_block));
        }

        auto const starting_checkpoint =
            starting_block / monad::db::as_string<TDB>();

        if (!fs::exists(starting_checkpoint)) {
            return tl::make_unexpected(fmt::format(
                "{} starting checkpoint is missing {}",
                __PRETTY_FUNCTION__,
                starting_checkpoint));
        }

        fs::copy(starting_checkpoint, path);
    }

    return path;
}

MONAD_DB_NAMESPACE_END
