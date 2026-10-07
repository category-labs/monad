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

// Measure witness composition by parsing the finished blob, independently of
// the generator. Node encodings must tile it exactly.
//
// On 504 mainnet witnesses, digests accounted for 82% of blob bytes; witness
// bytes correlated with COST at R2 0.942. Code bytes added no explanatory
// value after leaf count. Count both to test that relationship on other
// corpora; these are measurements, not a universal cost model.

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

        /// Bytes per node tag. Variable-length paths require parsing; summing
        /// these widths must reconstruct the blob length exactly.
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
