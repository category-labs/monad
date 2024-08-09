#pragma once

#include <monad/config.hpp>
#include <monad/db/file_db.hpp>

#include <cstdint>
#include <filesystem>

MONAD_NAMESPACE_BEGIN

struct Block;

class BrotliBlockDb
{
    FileDb db_;

public:
    BrotliBlockDb(std::filesystem::path const &);

    bool get(uint64_t, Block &) const;

    void upsert(uint64_t, Block const &) const;
    bool remove(uint64_t) const;
};

MONAD_NAMESPACE_END
