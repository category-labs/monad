#pragma once

#include <monad/chain/chain.hpp>
#include <monad/config.hpp>
#include <monad/db/file_db.hpp>

#include <cstdint>
#include <filesystem>

MONAD_NAMESPACE_BEGIN

struct Block;

class BlockDb
{
    FileDb db_;
    Chain const &chain_;

public:
    BlockDb() = delete;
    BlockDb(Block const &) = delete;
    BlockDb(BlockDb &&) = default;
    explicit BlockDb(std::filesystem::path const &, Chain const &);
    ~BlockDb() = default;

    bool get(uint64_t, Block &) const;

    void upsert(uint64_t, Block const &) const;
    bool remove(uint64_t) const;
};

MONAD_NAMESPACE_END
