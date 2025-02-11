#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash.hpp>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

class BlockHashChain : public BlockHash
{
    mpt::Db const &db_;
    uint64_t block_;
    uint64_t round_;

public:
    BlockHashChain(mpt::Db const &);
    bytes32_t get(uint64_t) const override;
    void set_block_and_round(uint64_t block, std::optional<uint64_t> round);
};

MONAD_NAMESPACE_END
