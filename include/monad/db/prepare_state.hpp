#pragma once

#include <monad/core/assert.h>
#include <monad/db/concepts.hpp>
#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <quill/bundled/fmt/format.h>

#include <tl/expected.hpp>

#include <concepts>
#include <filesystem>

namespace fmt = fmtquill::v10;

MONAD_DB_NAMESPACE_BEGIN

template <typename TDB>
[[nodiscard]] inline tl::expected<std::filesystem::path, std::string>
find_starting_checkpoint(
    std::filesystem::path root, uint64_t starting_block_number)
{
    namespace fs = std::filesystem;

    MONAD_DEBUG_ASSERT(starting_block_number);

    auto const starting_block =
        root / std::to_string(starting_block_number - 1);

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

    return starting_checkpoint;
}

// Preparing initial db state and return the path for opening. If preparation
// fails, return a string explanation
template <
    template <typename TExecutor, Permission TPermission> typename TDB,
    typename TExecutor, Permission TPermission>
    requires Writable<TPermission>
[[nodiscard]] inline tl::expected<std::filesystem::path, std::string>
prepare_state(std::filesystem::path root, uint64_t starting_block_number)
{
    namespace fs = std::filesystem;
    using db_t = TDB<TExecutor, TPermission>;

    auto const current_dir = root / detail::CURRENT_DATABASE;

    // overwrite CURRENT if exists
    if (fs::exists(current_dir)) {
        fs::remove_all(current_dir);
    }

    fs::create_directories(current_dir);

    auto const path = current_dir / monad::db::as_string<db_t>();
    if (starting_block_number) {
        return find_starting_checkpoint<db_t>(root, starting_block_number)
            .map([&](auto const &starting_checkpoint) {
                fs::copy(starting_checkpoint, path);
                return path;
            });
    }
    return path;
}

MONAD_DB_NAMESPACE_END
