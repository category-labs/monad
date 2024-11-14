#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>

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
    uint64_t last_finalized_round_;

    struct Proposal
    {
        uint64_t round;
        uint64_t parent_round;
        BlockHashBufferProposal buf;
    };

    std::deque<Proposal> proposals_;

public:
    BlockHashChain(
        BlockHashBufferFinalized &, uint64_t last_finalized_round = 0);
    void propose(bytes32_t const &, uint64_t round, uint64_t parent_round);
    void finalize(uint64_t const round);
    BlockHashBuffer const &find_chain(uint64_t) const;
};

bool init_block_hash_buffer_from_triedb(
    mpt::Db &, uint64_t, BlockHashBufferFinalized &);
bool init_block_hash_buffer_from_blockdb(
    BlockDb &, uint64_t, BlockHashBufferFinalized &);

MONAD_NAMESPACE_END
