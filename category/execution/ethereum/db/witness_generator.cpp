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

#include <category/execution/ethereum/db/witness_generator.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/util.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>
#include <boost/container/static_vector.hpp>

#include <array>
#include <cstdint>
#include <cstring>
#include <deque>
#include <memory>
#include <utility>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using ::monad::mpt::INVALID_BRANCH;
using ::monad::mpt::Nibbles;
using ::monad::mpt::NibblesView;
using ::monad::mpt::Node;

/// Shadow Trie used to encode which paths were accessed in the current block
/// i.e. if children[nibble] != nullptr
/// The trie also records delete paths, i.e. that lead to leaves
/// deleted in this block.
struct AccessNode
{
    std::array<std::unique_ptr<AccessNode>, 16> children{};
    /// True on every node strictly below the anchor of a `mark_delete_path`
    /// walk — i.e. nodes that may end up as the surviving sibling when
    /// commit's `trie_delete` collapses a branch. The anchor itself
    /// (the receiver of `mark_delete_path`) stays unmarked, so a slot
    /// zero-out under an otherwise-live account doesn't pollute
    /// emission of the accounts-trie path above the account leaf.
    bool delete_path{false};

    /// Walk `path` from this node, creating children as needed, and
    /// return a reference to the terminal node. Returning the terminus
    /// lets callers mark storage slots in the account subtrie.
    AccessNode &mark(NibblesView const path)
    {
        AccessNode *cur = this;
        for (unsigned i = 0; i < path.nibble_size(); ++i) {
            auto &child = cur->children[path.get(i)];
            if (!child) {
                child = std::make_unique<AccessNode>();
            }
            cur = child.get();
        }
        return *cur;
    }

    /// Same shape as `mark`, but additionally tags every node walked
    /// into with `delete_path=true`. The root is left unmarked.
    AccessNode &mark_delete_path(NibblesView const path)
    {
        AccessNode *cur = this;
        for (unsigned i = 0; i < path.nibble_size(); ++i) {
            auto &child = cur->children[path.get(i)];
            if (!child) {
                child = std::make_unique<AccessNode>();
            }
            cur = child.get();
            cur->delete_path = true;
        }
        return *cur;
    }
};

/// `bytes32_t` viewed as a 64-nibble sequence.
NibblesView nibbles_of(bytes32_t const &b)
{
    return NibblesView{byte_string_view{b.bytes, sizeof(b.bytes)}};
}

AccessNode build_access_trie(
    StateDeltas const &deltas,
    SelfDestructStorageReads const &self_destruct_storage_reads)
{
    AccessNode root;
    for (auto const &[addr, state_delta] : deltas) {
        bytes32_t const addr_hash =
            to_bytes(keccak256({addr.bytes, sizeof(addr.bytes)}));
        auto const &account = state_delta.account;
        bool const selfdestruct =
            account.first.has_value() && !account.second.has_value();
        AccessNode &acct_node =
            selfdestruct ? root.mark_delete_path(nibbles_of(addr_hash))
                         : root.mark(nibbles_of(addr_hash));
        if (!selfdestruct) {
            for (auto const &[slot, sdelta] : state_delta.storage) {
                bytes32_t const slot_hash =
                    to_bytes(keccak256({slot.bytes, sizeof(slot.bytes)}));
                bool const zero_out =
                    sdelta.first != bytes32_t{} && sdelta.second == bytes32_t{};
                if (zero_out) {
                    acct_node.mark_delete_path(nibbles_of(slot_hash));
                }
                else {
                    acct_node.mark(nibbles_of(slot_hash));
                }
            }
        }
    }
    // Slots read before a SELFDESTRUCT need to be added to the witness.
    for (auto const &[addr, slots] : self_destruct_storage_reads) {
        bytes32_t const addr_hash =
            to_bytes(keccak256({addr.bytes, sizeof(addr.bytes)}));
        AccessNode &acct_node = root.mark(nibbles_of(addr_hash));
        for (auto const &slot : slots) {
            bytes32_t const slot_hash =
                to_bytes(keccak256({slot.bytes, sizeof(slot.bytes)}));
            acct_node.mark(nibbles_of(slot_hash));
        }
    }
    return root;
}

/// Emits the offset-format node blob (offset_trie.hpp §4) for every node
/// in the live accounts trie that lies on a path to a touched (account or
/// slot) leaf. Nodes are written in post-order, so every child offset is
/// strictly less than the offset of the node referencing it.
///
/// Unlike an RLP branch — which carries all 16 child hashes inline, letting
/// the verifier synthesise its own stubs — an offset branch holds bare
/// offsets. So every untouched child must be written out explicitly as a
/// Digest node carrying its hash.
///
/// The access trie cursor follows the live traversal in lockstep:
/// `should_visit(branch)` reduces to "does the current cursor have a
/// child for this nibble?".
class WitnessEmitMachine final : public mpt::TraverseMachine
{
    byte_string &out_;
    mpt::NodeId root_id_{mpt::NULL_ID};

    struct Frame
    {
        /// Cursor into the access trie, recording touched parts of the MPT in
        /// the execution of a block. `nullptr` means this subtree was not
        /// accessed in the block execution
        AccessNode const *cursor;

        unsigned consumed_nibbles{0};
        bool single_branch{false};
        uint8_t sibling_count{0};
        /// initially popcount of node.mask at this level — total live children.
        uint8_t live_count{0};
        /// Offsets of this node's emitted children, by nibble. Filled in by
        /// each child's `up()`; NULL_ID until then.
        std::array<mpt::NodeId, 16> child_id{};
        /// The canonical path this node is emitted with, fused with the
        /// incoming branch nibble when the parent was a single-child node.
        Nibbles path;
    };

    std::deque<Frame> frames_;

    /// Append one node and return the offset it was written at, which is its
    /// NodeId
    mpt::NodeId emit(auto &&write)
    {
        auto const id = mpt::NodeId{static_cast<uint32_t>(out_.size())};
        write();
        return id;
    }

public:
    WitnessEmitMachine(AccessNode const &root, byte_string &out)
        : out_{out}
    {
        frames_.emplace_back(&root);
    }

    mpt::NodeId root_id() const
    {
        return root_id_;
    }

    /// Visit-order factory passed to `preorder_traverse_blocking`. Returns
    /// children of the current node ordered so that delete-path subtrees
    /// are descended into before the rest, matching the order the witness
    /// emitter expects. The returned `static_vector` owns its storage so
    /// the recursive descent below cannot clobber it.
    boost::container::static_vector<std::pair<uint8_t, unsigned char>, 16>
    children_iter_order(uint16_t const mask) const
    {
        boost::container::static_vector<std::pair<uint8_t, unsigned char>, 16>
            out;
        auto const &frame = frames_.back();

        if (frame.cursor) {
            for (auto const [idx, b] : mpt::NodeChildrenRange(mask)) {
                auto const &c = frame.cursor->children[b];
                if (c && c->delete_path) {
                    out.push_back({idx, b});
                }
            }
            for (auto const [idx, b] : mpt::NodeChildrenRange(mask)) {
                auto const &c = frame.cursor->children[b];
                if (!(c && c->delete_path)) {
                    out.push_back({idx, b});
                }
            }
        }
        else {
            for (auto const [idx, b] : mpt::NodeChildrenRange(mask)) {
                out.push_back({idx, b});
            }
        }
        MONAD_ASSERT(out.size() == frame.sibling_count);

        return out;
    }

    /// Walk the access cursor down by `path` nibbles. Always advances
    /// `consumed_nibbles` by the full path length; the access cursor
    /// may go null mid-walk.
    void walk_cursor(NibblesView const path)
    {
        auto &frame = frames_.back();
        for (unsigned i = 0; i < path.nibble_size(); ++i) {
            if (frame.cursor != nullptr) {
                frame.cursor = frame.cursor->children[path.get(i)].get();
            }
            ++frame.consumed_nibbles;
        }
    }

    void walk_cursor(unsigned char const nibble)
    {
        auto &frame = frames_.back();
        if (frame.cursor != nullptr) {
            frame.cursor = frame.cursor->children[nibble].get();
        }
        ++frame.consumed_nibbles;
    }

    bool should_visit(Node const &node, unsigned char const branch) override
    {
        auto const &frame = frames_.back();
        // Force descent into a stashed fusion target. `single_branch`
        // is set when a single-child node needs to be fused with its
        // child to form a canonical extension/leaf.
        if (frame.single_branch) {
            return true;
        }
        if (frame.cursor != nullptr &&
            frame.cursor->children[branch] != nullptr) {
            return true;
        }
        // Emit a single surviving child of a branch.
        // This is needed for branch compression
        if (frame.live_count == 1 && frame.sibling_count > frame.live_count) {
            return true;
        }
        // A child the trie references inline (canonical RLP < 32 B) has no
        // hash to put in a Digest, and the reader hash-references every
        // Digest it sees — stubbing one would change the parent's encoding.
        // Materialise it instead; such subtrees are tiny by construction.
        if (node.child_data_view(node.to_child_index(branch)).size() <
            KECCAK256_SIZE) {
            return true;
        }
        return false;
    }

    static mpt::NodeId sole_child_id(Frame const &frame)
    {
        for (mpt::NodeId const id : frame.child_id) {
            if (id != mpt::NULL_ID) {
                return id;
            }
        }
        MONAD_ABORT("single-child node with no emitted child");
    }

    /// Write a Digest for every live child we chose not to descend into.
    /// Emitted before the parent, so their offsets stay backward.
    void emit_digests(Node const &node, Frame &frame)
    {
        for (auto const [idx, b] : mpt::NodeChildrenRange(node.mask)) {
            if (frame.child_id[b] != mpt::NULL_ID) {
                continue;
            }
            auto const ref = node.child_data_view(idx);
            // should_visit() forces descent into inline-referenced children,
            // so anything still unvisited here is hash-referenced.
            MONAD_ASSERT(ref.size() == KECCAK256_SIZE);
            bytes32_t hash;
            std::memcpy(hash.bytes, ref.data(), KECCAK256_SIZE);
            frame.child_id[b] = emit([&] { mpt::append_digest(out_, hash); });
        }
    }

    /// Mirrors the canonical ext/branch split: a single-child node becomes an
    /// extension straight to its child, a multi-child node a branch, wrapped
    /// in an extension when it carries a path.
    mpt::NodeId emit_ext_or_branch(Node const &node, Frame const &frame)
    {
        if (node.number_of_children() == 1) {
            MONAD_ASSERT(frame.path.nibble_size() > 0);
            mpt::NodeId const child = sole_child_id(frame);
            return emit([&] { mpt::append_ext(out_, frame.path, child); });
        }
        MONAD_ASSERT(node.number_of_children() > 1);
        mpt::NodeId const branch =
            emit([&] { mpt::append_branch(out_, frame.child_id); });
        if (frame.path.nibble_size() == 0) {
            return branch;
        }
        return emit([&] { mpt::append_ext(out_, frame.path, branch); });
    }

    /// The slot value as the format stores it: raw 32 bytes, big-endian.
    static bytes32_t storage_value(Node const &node)
    {
        byte_string_view enc = node.value();
        auto const v = decode_storage_db_ignore_key(enc);
        MONAD_ASSERT(!v.has_error());
        MONAD_ASSERT(v.value().size() <= sizeof(bytes32_t));
        bytes32_t value;
        std::memcpy(
            value.bytes + (sizeof(bytes32_t) - v.value().size()),
            v.value().data(),
            v.value().size());
        return value;
    }

    mpt::NodeId emit_node(Node const &node, Frame &frame)
    {
        constexpr unsigned ACCOUNT_LEAF_DEPTH = KECCAK256_SIZE * 2;

        emit_digests(node, frame);

        // Walking account trie
        if (frame.consumed_nibbles < ACCOUNT_LEAF_DEPTH) {
            return emit_ext_or_branch(node, frame);
        }
        if (frame.consumed_nibbles == ACCOUNT_LEAF_DEPTH) {
            MONAD_ASSERT(node.has_value());
            // The storage subtree becomes an explicit edge, so its root must
            // precede the leaf pointing at it.
            mpt::NodeId storage = mpt::NULL_ID;
            if (node.number_of_children() > 1) {
                storage =
                    emit([&] { mpt::append_branch(out_, frame.child_id); });
            }
            else if (node.number_of_children() == 1) {
                storage = sole_child_id(frame);
            }
            byte_string const acct_rlp = AccountLeafProcessor::process(node);
            return emit([&] {
                mpt::append_acct_raw(out_, frame.path, acct_rlp, storage);
            });
        }
        // Walking account storage trie
        if (frame.consumed_nibbles < 2 * ACCOUNT_LEAF_DEPTH) {
            return emit_ext_or_branch(node, frame);
        }
        MONAD_ASSERT(frame.consumed_nibbles == 2 * ACCOUNT_LEAF_DEPTH);
        MONAD_ASSERT(node.has_value() && !node.value().empty());
        MONAD_ASSERT(node.number_of_children() == 0);
        return emit([&] {
            mpt::append_storage(out_, frame.path, storage_value(node));
        });
    }

    bool down(unsigned char const branch_nibble, Node const &node) override
    {
        if (branch_nibble == INVALID_BRANCH) {

            MONAD_ASSERT(node.path_nibble_view().nibble_size() == 0);
            MONAD_ASSERT(node.has_value() && node.value().empty());
            MONAD_ASSERT(frames_.back().consumed_nibbles == 0);
            // empty accounts trie
            if (node.number_of_children() == 0) {
                return false;
            }
            if (node.number_of_children() == 1) {
                auto &root_frame = frames_.back();
                root_frame.sibling_count =
                    static_cast<uint8_t>(__builtin_popcount(node.mask));
                root_frame.live_count = root_frame.sibling_count;
                root_frame.single_branch = true;
                return true;
            }
        }
        else {
            // Inherit the parent frame. Safe to construct straight from
            // back(): a deque never relocates existing elements on push.
            frames_.emplace_back(frames_.back());
            frames_.back().child_id = {};
            frames_.back().path = {};
            walk_cursor(branch_nibble);
        }

        walk_cursor(node.path_nibble_view());

        auto &frame = frames_.back();
        frame.sibling_count =
            static_cast<uint8_t>(__builtin_popcount(node.mask));
        frame.live_count = frame.sibling_count;

        // Stashed for up(), which does the emitting: the blob is post-ordered,
        // so a node cannot be written until its children have offsets.
        frame.path = frame.single_branch
                         ? concat(branch_nibble, node.path_nibble_view())
                         : Nibbles{node.path_nibble_view()};

        frame.single_branch = node.number_of_children() == 1;

        return true;
    }

    void up(unsigned char const branch_nibble, Node const &node) override
    {
        auto &frame = frames_.back();

        // The single-child section-root marker is fused away: down() emitted
        // nothing for it, and its child — which absorbed the branch nibble
        // into its own path — stands in as the trie root.
        bool const fused =
            branch_nibble == INVALID_BRANCH && node.number_of_children() == 1;
        mpt::NodeId const id =
            fused ? sole_child_id(frame) : emit_node(node, frame);

        bool branch_deleted = false;
        if (frame.cursor && frame.cursor->delete_path) {
            if (node.has_value()) {
                // On a delete_path, the leaf itself is the target
                branch_deleted = true;
            }
            else {
                // Internal node within a delete_path subtree — deleted iff
                // every live child was also deleted.
                branch_deleted = (frame.live_count == 0);
            }
        }
        frames_.pop_back();
        if (frames_.empty()) {
            root_id_ = id;
            return;
        }
        if (branch_deleted) {
            --frames_.back().live_count;
        }
        frames_.back().child_id[branch_nibble] = id;
    }

    std::unique_ptr<mpt::TraverseMachine> clone() const override
    {
        return std::make_unique<WitnessEmitMachine>(*this);
    }
};

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

WitnessData generate_witness(
    mpt::Db &db, mpt::NodeCursor const &accounts_trie_root,
    uint64_t const block_number, StateDeltas const &deltas,
    ankerl::unordered_dense::segmented_map<bytes32_t, vm::SharedIntercode> const
        &read_codes,
    SelfDestructStorageReads const &self_destruct_storage_reads)
{
    WitnessData wd;

    AccessNode const access_root =
        build_access_trie(deltas, self_destruct_storage_reads);

    // Header: magic + a root_off placeholder patched once the root's offset
    // is known. Nodes start at HEADER_LEN, so 0 stays a safe null sentinel.
    static constexpr unsigned char MAGIC[4] = {'M', 'Z', 'W', 0x01};
    wd.nodes.append(MAGIC, sizeof(MAGIC));
    wd.nodes.append(sizeof(uint32_t), 0);
    MONAD_ASSERT(wd.nodes.size() == mpt::HEADER_LEN);

    mpt::NodeId root_id = mpt::NULL_ID;
    if (accounts_trie_root.is_valid()) {
        WitnessEmitMachine machine{access_root, wd.nodes};
        MONAD_ASSERT(db.traverse_blocking(
            accounts_trie_root,
            machine,
            block_number,
            [&machine](uint16_t const mask) {
                return machine.children_iter_order(mask);
            }));
        root_id = machine.root_id();
    }
    auto const root_off = static_cast<uint32_t>(root_id);
    std::memcpy(wd.nodes.data() + 4, &root_off, sizeof(root_off));

    wd.codes.reserve(read_codes.size());
    for (auto const &[_hash, intercode] : read_codes) {
        auto const span = intercode->code_span();
        wd.codes.emplace_back(span.begin(), span.end());
    }

    return wd;
}

MONAD_NAMESPACE_END
