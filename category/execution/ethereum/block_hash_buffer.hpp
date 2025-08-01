#pragma once

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/chain/chain_config.h>

#include <cstdint>
#include <deque>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockDb;

namespace mpt
{
    class Db;
}

class BlockHashBuffer
{
public:
    static constexpr unsigned N = 256;

    virtual uint64_t n() const = 0;
    virtual bytes32_t const &get(uint64_t) const = 0;
    virtual ~BlockHashBuffer() = default;
};

class BlockHashBufferFinalized : public BlockHashBuffer
{
    bytes32_t b_[N];
    uint64_t n_;

public:
    BlockHashBufferFinalized();

    uint64_t n() const override;
    bytes32_t const &get(uint64_t) const override;

    void set(uint64_t, bytes32_t const &);
};

class BlockHashBufferProposal : public BlockHashBuffer
{
    uint64_t n_;
    BlockHashBuffer const *buf_;
    std::vector<bytes32_t> deltas_;

public:
    BlockHashBufferProposal(
        bytes32_t const &, BlockHashBufferFinalized const &);
    BlockHashBufferProposal(bytes32_t const &, BlockHashBufferProposal const &);

    uint64_t n() const override;
    bytes32_t const &get(uint64_t) const override;
};

class BlockHashChain
{
    BlockHashBufferFinalized &buf_;

    struct Proposal
    {
        uint64_t block_number;
        bytes32_t block_id;
        bytes32_t parent_id;
        BlockHashBufferProposal buf;
    };

    std::deque<Proposal> proposals_;

public:
    BlockHashChain(BlockHashBufferFinalized &);

    void propose(
        bytes32_t const &, uint64_t block_number, bytes32_t const &block_id,
        bytes32_t const &parent_id);
    void finalize(bytes32_t const &block_id);
    BlockHashBuffer const &find_chain(bytes32_t const &block_id) const;
};

bool init_block_hash_buffer_from_triedb(
    mpt::Db &, uint64_t, BlockHashBufferFinalized &);

bool init_block_hash_buffer_from_blockdb(
    monad_chain_config const, BlockDb &, uint64_t block_number,
    BlockHashBufferFinalized &);

MONAD_NAMESPACE_END
