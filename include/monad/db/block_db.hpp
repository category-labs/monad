#pragma once

#include <monad/core/block.hpp>

#include <monad/db/config.hpp>
#include <monad/db/file_db.hpp>

#include <filesystem>

MONAD_DB_NAMESPACE_BEGIN

class BlockDb
{
public:
    BlockDb(std::filesystem::path const &block_db_path)
        : db_{block_db_path.c_str()} {};
    ~BlockDb() = default;

    enum class Status
    {
        SUCCESS,
        NO_BLOCK_FOUND,
        DECOMPRESS_ERROR,
        DECODE_ERROR
    };

    [[nodiscard]] Status get(block_num_t const block_num, Block &block) const;

private:
    FileDb db_;
};

MONAD_DB_NAMESPACE_END