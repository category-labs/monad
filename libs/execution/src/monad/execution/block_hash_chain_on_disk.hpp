#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash_buffer.hpp>
#include <monad/lru/lru_cache.hpp>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

class BlockHashChainOnDisk : public BlockHashBuffer
{
    mpt::Db const &db_;
    uint64_t block_;
    std::optional<uint64_t> round_;

public:
    BlockHashChainOnDisk(mpt::Db const &);
    bytes32_t get(uint64_t) const override;
    uint64_t n() const override;
    void set_block_and_round(uint64_t block, std::optional<uint64_t> round);
};

MONAD_NAMESPACE_END