#pragma once

#include <monad/db/config.hpp>
#include <monad/db/util.hpp>

#include <quill/bundled/fmt/format.h>
#include <quill/bundled/fmt/std.h>

#include <rocksdb/db.h>
#include <rocksdb/utilities/checkpoint.h>

#include <tl/expected.hpp>

#include <filesystem>
#include <iostream>
#include <memory>

namespace fmt = fmtquill::v10;

MONAD_DB_NAMESPACE_BEGIN

[[nodiscard]] inline tl::expected<void, std::string>
create_and_prune_block_history(
    std::filesystem::path root, std::shared_ptr<rocksdb::DB> db,
    uint64_t block_number, uint64_t block_history_size)
{
    namespace fs = std::filesystem;

    auto const block_dir = root / std::to_string(block_number);
    fs::create_directories(block_dir);

    auto const stem = std::filesystem::path(db->GetName()).stem();
    auto const checkpoint_dir = block_dir / stem;

    if (fs::exists(checkpoint_dir)) {
        fs::remove_all(checkpoint_dir);
    }

    rocksdb::Checkpoint *checkpoint;
    auto status = rocksdb::Checkpoint::Create(db.get(), &checkpoint);
    if (!status.ok()) {
        return tl::make_unexpected(status.ToString());
    }

    std::unique_ptr<rocksdb::Checkpoint> ucp{checkpoint};
    status = checkpoint->CreateCheckpoint(checkpoint_dir);
    if (!status.ok()) {
        return tl::make_unexpected(status.ToString());
    }

    // Remove the checkpoint that fell just outside of the historical range
    if (block_number > block_history_size) {
        fs::remove_all(
            root / std::to_string(block_number - block_history_size));
    }

    return {};
}

MONAD_DB_NAMESPACE_END
