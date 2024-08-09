#pragma once

#include <monad/config.hpp>
#include <monad/db/file_db.hpp>

#include <cstdint>
#include <filesystem>

MONAD_NAMESPACE_BEGIN

struct Block;

struct BlockDb
{
    virtual std::optional<Block> read_block(uint64_t) const = 0;
};

class BrotliBlockDb : public BlockDb
{
    FileDb db_;

public:
    BrotliBlockDb(std::filesystem::path const &);

    virtual std::optional<Block> read_block(uint64_t) const override;

    void upsert(uint64_t, Block const &) const;
    bool remove(uint64_t) const;
};

MONAD_NAMESPACE_END
