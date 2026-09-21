// Copyright (C) 2026 Category Labs, Inc.
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

// The blocks the corpus is made of. Each scenario seeds its own genesis and
// returns its blocks, so a caller runs one or runs all of them.

#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <zkvm/test/corpus/corpus_builder.hpp>

#include <cstdint>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    /// Keys are derived from a seed so a regenerated corpus is byte-identical:
    /// libsecp256k1 signs with RFC6979, so the same key over the same preimage
    /// gives the same signature.
    bytes32_t derive_key(bytes32_t const &seed, uint64_t index);

    struct Scenario
    {
        std::string name;
        /// Seeds genesis, then returns the blocks to run against it.
        std::function<void(State &)> genesis;
        std::function<std::vector<BlockSpec>(CorpusBuilder &)> blocks;
    };

    /// transfers: EOA-to-EOA value movement plus a contract that writes,
    /// rewrites and zeroes storage slots. The zeroing is the interesting part
    /// -- it collapses a storage branch, which is the case generate_witness
    /// has to cover with a Digest.
    ///
    /// evm: CREATE, logs, REVERT, SELFDESTRUCT, and the transaction types
    /// (legacy, 2930, 1559).
    ///
    /// spoke: deploys the real NamespaceSpoke and sends namespace messages
    /// through it, so the L2 anchor work has logs to harvest and a pending
    /// array to clear.
    std::vector<Scenario> all_scenarios(bytes32_t const &seed);
}

MONAD_NAMESPACE_END
