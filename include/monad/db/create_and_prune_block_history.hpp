#pragma once

#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <fmt/format.h>
#include <fmt/std.h>
#include <rocksdb/db.h>
#include <rocksdb/utilities/checkpoint.h>
#include <tl/expected.hpp>

#include <filesystem>
#include <iostream>
#include <memory>

MONAD_DB_NAMESPACE_BEGIN

template <typename TDB>
[[nodiscard]] inline tl::expected<void, std::string>
create_and_prune_block_history(TDB const &db, uint64_t block_number)
{
    namespace fs = std::filesystem;

    auto const block_dir = db.root / std::to_string(block_number);
    fs::create_directories(block_dir);

    auto const checkpoint_dir = block_dir / monad::db::as_string<TDB>();

    if (fs::exists(checkpoint_dir)) {
        fs::remove_all(checkpoint_dir);
    }

    rocksdb::Checkpoint *checkpoint;
    auto status = rocksdb::Checkpoint::Create(db.db.get(), &checkpoint);
    if (!status.ok()) {
        return tl::make_unexpected(status.ToString());
    }

    std::unique_ptr<rocksdb::Checkpoint> ucp{checkpoint};
    status = checkpoint->CreateCheckpoint(checkpoint_dir);
    if (!status.ok()) {
        return tl::make_unexpected(status.ToString());
    }

    // Remove the checkpoint that fell just outside of the historical range
    if (block_number > db.block_history_size) {
        fs::remove_all(
            db.root / std::to_string(block_number - db.block_history_size));
    }

    return {};
}

MONAD_DB_NAMESPACE_END
