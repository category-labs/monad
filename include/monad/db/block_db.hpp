#pragma once

#include <monad/db/block_db_interface.hpp>
#include <monad/db/file_db.hpp>

#include <filesystem>
#include <memory>

MONAD_DB_NAMESPACE_BEGIN

class BlockDb : IBlockDb
{
public:
    BlockDb(std::filesystem::path const &block_db_path)
        : db_{block_db_path.c_str()} {};
    ~BlockDb() = default;

    [[nodiscard]] bool get(block_num_t block_num, Block &block) const override;

private:
    FileDb db_;
};

MONAD_DB_NAMESPACE_END