#pragma once

#include <monad/config.hpp>

#include <monad/db/file_db.hpp>

#include <silkworm/common/base.hpp>
#include <silkworm/types/block.hpp>

#include <filesystem>

MONAD_NAMESPACE_BEGIN

class BlockDb
{
    FileDb db_;

public:
    BlockDb(std::filesystem::path const &);

    bool get(silkworm::BlockNum, silkworm::Block &) const;

    void upsert(silkworm::BlockNum, silkworm::Block const &) const;
    void remove(silkworm::BlockNum) const;
};

MONAD_NAMESPACE_END
