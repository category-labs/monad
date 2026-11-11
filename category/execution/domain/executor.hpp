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
#include <category/execution/domain/execute_domain_block.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

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

struct DerivedDomainBlock;

// Executes one private domain's blocks, in order, into the domain's own triedb.
// Each block is finalized as soon as it commits, because blocks are derived
// from finalized L1 blocks only.
class PrivateDomainExecutor
{
    DomainChain chain_;
    TrieDb db_;
    vm::VM &vm_;
    fiber::PriorityPool &priority_pool_;
    BlockHashBufferFinalized block_hashes_;
    uint64_t next_block_{0};

    template <Traits traits>
        requires is_monad_trait_v<traits>
    Result<void> execute_block(DerivedDomainBlock const &);

public:
    // Executes as the domain `domain_chain_id` of the L1 `l1_chain`, and
    // continues after the db's latest finalized block. The db must match
    // the encoding of the blocks' revisions.
    PrivateDomainExecutor(
        MonadChain const &l1_chain, uint64_t domain_chain_id, mpt::Db &,
        vm::VM &, fiber::PriorityPool &);

    uint64_t next_block() const
    {
        return next_block_;
    }

    // Executes `block`, which must be the next block. A block that fails to
    // execute is an error.
    Result<void> execute(DerivedDomainBlock const &block);
};

MONAD_DOMAIN_NAMESPACE_END
