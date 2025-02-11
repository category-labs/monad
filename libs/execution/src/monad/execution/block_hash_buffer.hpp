#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/execution/block_hash.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{
    class Db;
}

class BlockHashBuffer : public BlockHash
{
    bytes32_t b_[N];
    uint64_t n_;

public:
    BlockHashBuffer();

    bytes32_t get(uint64_t) const override;
    void set(uint64_t, bytes32_t const &);
};

bool init_block_hash_buffer_from_triedb(mpt::Db &, uint64_t, BlockHashBuffer &);

MONAD_NAMESPACE_END
