// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/bytes.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

struct MonadChain;

namespace fiber
{
    class PriorityPool;
}

namespace mpt
{
    class Db;
}

namespace vm
{
    class VM;
}

MONAD_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

class DomainBlockStore;
struct DomainBlock;

// Executes one private domain's stored blocks, in order, into the domain's
// own triedb, laid out like an L1 node's. Each block commits its state, code,
// receipts, transactions and Ethereum header through commit_block on
// the L1's proposal path, under its domain_block_id, and is finalized at
// once.
class PrivateDomainExecutor
{
    MonadChain const &l1_chain_;
    uint64_t domain_chain_id_;
    DomainBlockStore const &store_;
    TrieDb db_;
    vm::VM &vm_;
    fiber::PriorityPool &priority_pool_;
    BlockHashBufferFinalized block_hashes_;
    BlockHashChain block_hash_chain_;
    uint64_t next_block_{0};

    template <Traits traits>
        requires is_monad_trait_v<traits>
    Result<void> execute(DomainBlock const &);

public:
    // Executes as the domain `domain_chain_id`, which CHAINID returns, and
    // continues after the db's latest finalized block. The db must match
    // the encoding of the blocks' revisions.
    PrivateDomainExecutor(
        MonadChain const &, uint64_t domain_chain_id, DomainBlockStore const &,
        mpt::Db &, vm::VM &, fiber::PriorityPool &);

    uint64_t next_block() const
    {
        return next_block_;
    }

    // Executes the next block if the store has it, and returns whether it
    // did. A block that fails to execute is an error.
    Result<bool> execute_next();
};

MONAD_DOMAIN_NAMESPACE_END
