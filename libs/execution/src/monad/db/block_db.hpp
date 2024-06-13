#pragma once

#include <monad/config.hpp>
#include <monad/db/file_db.hpp>

#include <cstdint>
#include <filesystem>

MONAD_NAMESPACE_BEGIN

struct Block;

class BlockDb
{
public:
    enum class BlockCompression {
        None,
        Brotli
    };

private:
    FileDb db_;
    BlockCompression compression_;

public:
    BlockDb(std::filesystem::path const &,
            BlockCompression = BlockCompression::Brotli);

    bool get(uint64_t, Block &) const;

    void upsert(uint64_t, Block const &) const;
    bool remove(uint64_t) const;
};

MONAD_NAMESPACE_END
