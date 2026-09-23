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

#include <zkvm/test/corpus/witness_stats.hpp>

#include <category/core/assert.h>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    WitnessStats witness_stats(byte_string_view const witness)
    {
        WitnessStats st{};
        st.witness_bytes = witness.size();

#ifdef MONAD_ZKVM_L2
        auto const parsed = parse_execution_witness_l2(witness);
        MONAD_ASSERT(!parsed.has_error());
        auto const &w = parsed.value().base;
#else
        auto const parsed = parse_execution_witness(witness);
        MONAD_ASSERT(!parsed.has_error());
        auto const &w = parsed.value();
#endif
        st.block_bytes = w.block_rlp.size();
        st.blob_bytes = w.encoded_nodes.size();
        st.code_bytes = w.encoded_codes.size();
        st.ancestor_bytes = w.encoded_headers.size();

        // Walk the blob the way the guest's reader does: each node's length
        // comes from its own tag, so the run of nodes must land exactly on the
        // end. checked_end aborts if a node would reach past it, and the loop
        // can only exit level with it -- so an off-by-one grammar shows up as
        // an abort here rather than as a plausible count downstream.
        unsigned char const *const base = w.encoded_nodes.data();
        unsigned char const *const end = base + w.encoded_nodes.size();
        MONAD_ASSERT(w.encoded_nodes.size() >= mpt::HEADER_LEN);
        MONAD_ASSERT(
            base[0] == 'M' && base[1] == 'Z' && base[2] == 'W' &&
            base[3] == 0x01);

        for (unsigned char const *p = base + mpt::HEADER_LEN; p < end;) {
            mpt::NodeViewBase const node{p};
            auto const tag = node.tag();
            unsigned char const *const node_end = node.checked_end(end);
            auto const width = static_cast<size_t>(node_end - p);
            switch (tag) {
            case mpt::BRANCH:
                ++st.branches;
                st.branch_bytes += width;
                break;
            case mpt::EXT:
                ++st.exts;
                st.ext_bytes += width;
                break;
            case mpt::LEAF_ACCT:
                ++st.acct_leaves;
                st.acct_bytes += width;
                break;
            case mpt::LEAF_STORAGE:
                ++st.storage_leaves;
                st.storage_bytes += width;
                break;
            case mpt::DIGEST:
                ++st.digests;
                st.digest_bytes += width;
                break;
            default:
                MONAD_ABORT("witness_stats: invalid node tag");
            }
            p = node_end;
        }
        return st;
    }
}

MONAD_NAMESPACE_END
