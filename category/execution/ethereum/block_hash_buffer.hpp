// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/core/config.hpp>
#include <category/core/bytes.hpp>

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
    BlockDb &, uint64_t block_number, BlockHashBufferFinalized &);

MONAD_NAMESPACE_END
