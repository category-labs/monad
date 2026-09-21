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

// The producer's half of the node layout. See the declarations in
// offset_trie.hpp for why it sits beside the reader rather than beside the
// witness generator that calls it.

#include <category/execution/ethereum/db/offset_trie.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/nibble.h>
#include <category/core/rlp/encode.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>

// The file-local helpers sit in monad::{anonymous} as a SIBLING of monad::mpt,
// not nested inside it: MONAD_ANONYMOUS_NAMESPACE_BEGIN opens `namespace monad`
// of its own, so writing it inside MONAD_MPT_NAMESPACE_BEGIN would declare
// monad::mpt::monad::{anonymous}. Unqualified lookup from monad::mpt reaches
// out to monad, so the emitters below call these by their bare names.
MONAD_ANONYMOUS_NAMESPACE_BEGIN

using ::monad::mpt::NibblesView;
using ::monad::mpt::node_id_wire;
using ::monad::mpt::NodeId;
using ::monad::mpt::NodeViewBase;

void append_id(byte_string &out, NodeId const id)
{
    // The wire field is narrower than NodeId, which is why this is not a
    // memcpy of the enum: an id that does not fit is a producer bug, not
    // something to truncate silently.
    auto const v = static_cast<uint64_t>(id);
    MONAD_ASSERT(v <= UINT32_MAX);
    node_id_wire const w = static_cast<node_id_wire>(v);
    unsigned char buf[sizeof(node_id_wire)];
    std::memcpy(buf, &w, sizeof(buf)); // rv64im and x86 are both little-endian
    out.append(buf, sizeof(buf));
}

void append_path(byte_string &out, NibblesView const path)
{
    unsigned const nlen = path.nibble_size();
    MONAD_ASSERT(nlen <= 64);
    out.push_back(static_cast<unsigned char>(nlen));
    size_t const start = out.size();
    out.resize(start + (nlen + 1) / 2, 0);
    for (unsigned i = 0; i < nlen; ++i) {
        set_nibble(out.data() + start, i, path.get(i));
    }
}

// THE WRITER CHECKS ITSELF AGAINST THE READER. Both halves take their field
// positions from the same declarations, and this is what proves they agree on
// every node actually written: the reader's own extent has to land exactly on
// the bytes the emitter produced. A layout change that reaches only one half
// fails here, in debug, instead of shipping a blob the guest aborts on with
// nothing in the failure naming the cause.
void check_round_trip(byte_string const &out, size_t const start)
{
    MONAD_DEBUG_ASSERT(
        NodeViewBase{out.data() + start}.checked_end(out.data() + out.size()) ==
        out.data() + out.size());
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_MPT_NAMESPACE_BEGIN

void append_branch(byte_string &out, std::array<NodeId, 16> const &children)
{
    size_t const start = out.size();
    out.reserve(out.size() + 1 + 16 * sizeof(node_id_wire));
    out.push_back(BRANCH);
    for (NodeId const c : children) {
        append_id(out, c);
    }
    check_round_trip(out, start);
}

void append_ext(byte_string &out, NibblesView const path, NodeId const child)
{
    size_t const start = out.size();
    out.push_back(EXT);
    append_id(out, child);
    append_path(out, path);
    check_round_trip(out, start);
}

void append_storage(
    byte_string &out, NibblesView const path, bytes32_t const &value)
{
    size_t const start = out.size();
    out.push_back(LEAF_STORAGE);
    out.append(value.bytes, 32);
    append_path(out, path);
    check_round_trip(out, start);
}

// Decomposed rather than stored as the account's own RLP: the reader takes the
// storage root from the storage edge, so the leaf carries only the code hash,
// the nonce and the balance.
void append_acct(
    byte_string &out, NodeId const storage, Account const &acct,
    NibblesView const path)
{
    size_t const start = out.size();
    out.push_back(LEAF_ACCT);
    append_id(out, storage);
    out.append(rlp::encode_bytes32(acct.code_hash));
    // The length is known only once nonce and balance are encoded, and the
    // appends below may reallocate, so hold the slot by index and not by
    // pointer.
    size_t const len_index = out.size();
    out.push_back(0);
    out.append(rlp::encode_unsigned(acct.nonce));
    out.append(rlp::encode_unsigned(acct.balance));
    size_t const len = out.size() - len_index - 1;
    MONAD_ASSERT(len >= 2 && len <= MAX_NONCE_BALANCE_RLP_LEN);
    out[len_index] = static_cast<unsigned char>(len);
    append_path(out, path);
    check_round_trip(out, start);
}

void append_digest(byte_string &out, bytes32_t const &hash)
{
    size_t const start = out.size();
    out.push_back(DIGEST);
    out.append(hash.bytes, 32);
    check_round_trip(out, start);
}

MONAD_MPT_NAMESPACE_END
