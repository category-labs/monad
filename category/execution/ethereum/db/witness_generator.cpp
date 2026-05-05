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
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/compute.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/traverse.hpp>
#include <category/mpt/util.hpp>

#include <deque>
#include <memory>

#include <boost/container/static_vector.hpp>

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

struct NoValue
{
    static byte_string_view process(Node const &)
    {
        return {};
    }
};

/// Emits canonical Ethereum MPT RLP for every node visited in the live
/// accounts trie that lies on a path to a touched (account or slot) leaf.
/// Hash stubs for unvisited siblings are synthesised by the verifier from
/// the live parent's child-data view — the producer simply doesn't emit
/// them.
///
/// The access trie cursor follows the live traversal in lockstep:
/// `should_visit(branch)` reduces to "does the current cursor have a
/// child for this nibble?".
class WitnessEmitMachine final : public mpt::TraverseMachine
{
    std::vector<byte_string> &out_nodes_;

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
    };

    std::deque<Frame> frames_;

public:
    WitnessEmitMachine(
        AccessNode const &root, std::vector<byte_string> &out_nodes)
        : out_nodes_{out_nodes}
    {
        frames_.emplace_back(&root);
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

    bool should_visit(Node const &, unsigned char const branch) override
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
        return false;
    }

    void encode_ext_or_branch(Node const &node, NibblesView const ext_path)
    {
        if (node.number_of_children() == 1) {
            MONAD_ASSERT(ext_path.nibble_size() > 0);
            out_nodes_.push_back(mpt::encode_two_pieces(
                ext_path,
                node.child_data_view(0),
                /*has_value=*/false));
        }
        else {
            MONAD_ASSERT(node.number_of_children() > 1);

            byte_string branch_rlp = mpt::encode_branch<NoValue>(node);

            if (ext_path.nibble_size() > 0) {
                // branch wrapped in an extension

                if (MONAD_UNLIKELY(branch_rlp.size() < KECCAK256_SIZE)) {
                    out_nodes_.push_back(mpt::encode_two_pieces(
                        ext_path,
                        branch_rlp,
                        /*has_value=*/false));
                    return;
                }
                else {
                    auto const branch_ref = keccak256(branch_rlp);
                    out_nodes_.push_back(mpt::encode_two_pieces(
                        ext_path,
                        to_byte_string_view(branch_ref.bytes),
                        /*has_value=*/false));
                }
            }

            out_nodes_.push_back(std::move(branch_rlp));
        }
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
            frames_.push_back(auto(frames_.back()));
            walk_cursor(branch_nibble);
        }

        walk_cursor(node.path_nibble_view());

        auto &frame = frames_.back();
        frame.sibling_count =
            static_cast<uint8_t>(__builtin_popcount(node.mask));
        frame.live_count = frame.sibling_count;

        Nibbles const leaf_or_ext_path =
            frame.single_branch ? concat(branch_nibble, node.path_nibble_view())
                                : Nibbles{node.path_nibble_view()};

        constexpr unsigned ACCOUNT_LEAF_DEPTH = KECCAK256_SIZE * 2;

        // Walking account trie
        if (frame.consumed_nibbles < ACCOUNT_LEAF_DEPTH) {
            encode_ext_or_branch(node, leaf_or_ext_path);
        }
        else if (frame.consumed_nibbles == ACCOUNT_LEAF_DEPTH) {
            MONAD_ASSERT(node.has_value());
            out_nodes_.push_back(mpt::encode_two_pieces(
                leaf_or_ext_path,
                AccountLeafProcessor::process(node),
                /*has_value=*/true));
            if (node.number_of_children() > 1) {
                out_nodes_.push_back(mpt::encode_branch<NoValue>(node));
            }
        }
        // Walking account storage trie
        else if (frame.consumed_nibbles < 2 * ACCOUNT_LEAF_DEPTH) {
            encode_ext_or_branch(node, leaf_or_ext_path);
        }
        else {
            MONAD_ASSERT(frame.consumed_nibbles == 2 * ACCOUNT_LEAF_DEPTH);
            MONAD_ASSERT(node.has_value() && !node.value().empty());
            MONAD_ASSERT(node.number_of_children() == 0);
            out_nodes_.push_back(mpt::encode_two_pieces(
                leaf_or_ext_path,
                StorageLeafProcessor::process(node),
                /*has_value=*/true));
        }

        frame.single_branch = node.number_of_children() == 1;

        return true;
    }

    void up(unsigned char const, Node const &node) override
    {
        auto const &frame = frames_.back();
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
        if (branch_deleted && !frames_.empty()) {
            --frames_.back().live_count;
        }
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

    if (accounts_trie_root.is_valid()) {
        WitnessEmitMachine machine{access_root, wd.nodes};
        MONAD_ASSERT(db.traverse_blocking(
            accounts_trie_root,
            machine,
            block_number,
            [&machine](uint16_t const mask) {
                return machine.children_iter_order(mask);
            }));
    }

    wd.codes.reserve(read_codes.size());
    for (auto const &[_hash, intercode] : read_codes) {
        auto const span = intercode->code_span();
        wd.codes.emplace_back(span.begin(), span.end());
    }

    return wd;
}

MONAD_NAMESPACE_END
