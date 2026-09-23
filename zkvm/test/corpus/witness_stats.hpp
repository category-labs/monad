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

// What a witness is made of, counted after the fact.
//
// These are the regressors, and which ones they are is a measurement rather
// than a guess. Over 504 mainnet witnesses joined to their measured ZisK cost:
//
//   blob bytes = 40.0 x digests                 R2 0.9996
//   COST       = 2891 x witness bytes           R2 0.942   (2371..2734 per
//                                                           byte, 1st to 10th
//                                                           decile)
//   keccak     = 0.0093 x bytes^1.02            R2 0.987
//   COST       = 7.54e6 x touched leaves        R2 0.897
//   COST ~ leaves + code bytes                  delta-R2 0.000
//
// So a witness is its digests -- 82% of the blob's bytes are 33-byte hashes of
// siblings the block never touched -- and the blob's size is the cost, to
// within about 8% over a 40x range. Code bytes correlate with cost (R2 0.50)
// only because both track block size: given the leaf count they add nothing,
// which is why they are counted here to be ruled out rather than because they
// are expected to matter.
//
// Counting happens on the finished witness, not inside generate_witness. The
// blob is self-describing, so a walk needs nothing the generator would have to
// be taught to expose -- and the walk has a check an instrumented generator
// could not offer: the nodes must tile the blob exactly, end to end. A counter
// that had the grammar wrong would otherwise return plausible, wrong numbers.

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>

#include <cstddef>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    struct WitnessStats
    {
        /// Node counts, by tag.
        size_t branches{0};
        size_t exts{0};
        size_t acct_leaves{0};
        size_t storage_leaves{0};
        size_t digests{0};

        /// Bytes those nodes occupy, by tag. Branches and digests are fixed
        /// width; the other three carry a path, so only the walk knows their
        /// size. Kept so a test can reconstruct the blob's length exactly and
        /// catch a counter that drifted from the grammar.
        size_t branch_bytes{0};
        size_t ext_bytes{0};
        size_t acct_bytes{0};
        size_t storage_bytes{0};
        size_t digest_bytes{0};

        /// Field sizes of the RLP envelope.
        size_t block_bytes{0};
        size_t blob_bytes{0};
        size_t code_bytes{0};
        size_t ancestor_bytes{0};
        size_t witness_bytes{0};

        /// Header plus every node. Equals `blob_bytes` on a well-formed
        /// blob, which is what makes it a check rather than a restatement.
        size_t reconstructed_blob_bytes() const
        {
            return mpt::HEADER_LEN + branch_bytes + ext_bytes + acct_bytes +
                   storage_bytes + digest_bytes;
        }

        size_t nodes() const
        {
            return branches + exts + acct_leaves + storage_leaves + digests;
        }

        /// The leaves the block actually touched -- the dispersion measure.
        size_t touched_leaves() const
        {
            return acct_leaves + storage_leaves;
        }
    };

    /// Decode the envelope and tile the node blob. Aborts if the blob does not
    /// tile exactly, or if the envelope is not a witness.
    WitnessStats witness_stats(byte_string_view witness);
}

MONAD_NAMESPACE_END
