#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/block_db.hpp>
#include <monad/db/trie_db.hpp>

#include <cstdint>
#include <deque>
#include <vector>

MONAD_NAMESPACE_BEGIN

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
    uint64_t round_;
    uint64_t parent_round_;
    BlockHashBuffer const *buf_;
    std::vector<bytes32_t> deltas_;

public:
    BlockHashBufferProposal(
        bytes32_t const &, uint64_t, uint64_t,
        BlockHashBufferFinalized const &);
    BlockHashBufferProposal(
        bytes32_t const &, uint64_t, uint64_t, BlockHashBufferProposal const &);

    // needed for deque.erase()
    BlockHashBufferProposal(BlockHashBufferProposal &&) = default;
    BlockHashBufferProposal &operator=(BlockHashBufferProposal &&) = default;
    BlockHashBufferProposal(BlockHashBufferProposal &) = delete;
    BlockHashBufferProposal &operator=(BlockHashBufferProposal &) = delete;

    uint64_t n() const override;
    bytes32_t const &get(uint64_t) const override;

    uint64_t round() const;
    uint64_t parent_round() const;
    bytes32_t const &h() const;
};

class BlockHashChain
{
    BlockHashBufferFinalized &buf_;
    std::deque<BlockHashBufferProposal> proposals_;
    uint64_t finalized_;

public:
    BlockHashChain(BlockHashBufferFinalized &);

    BlockHashBuffer const &
    propose(bytes32_t const &, uint64_t round, uint64_t parent_round);
    BlockHashBuffer const &finalize(uint64_t const round);
    BlockHashBuffer const &find_chain(uint64_t parent_round) const;
};

bool init_block_hash_buffer(
    mpt::Db &rodb, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer);

bool init_block_hash_buffer(
    BlockDb &block_db, uint64_t const block_number,
    BlockHashBufferFinalized &block_hash_buffer);

MONAD_NAMESPACE_END
