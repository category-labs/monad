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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/partial_trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/decode.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

#include <array>
#include <cstdint>
#include <cstring>
#include <memory>
#include <span>
#include <utility>

MONAD_NAMESPACE_BEGIN

namespace
{

    // Forward declaration for mutual recursion.
    template <typename T>
    Result<ChildRef<T>> decode_child_ref(
        rlp::RlpType ty, byte_string_view &enc, mpt::NibblesView path,
        NodeIndex const &nodes);

    template <typename T>
    byte_string encode_child_ref(ChildRef<T> const &child);

    // ensures enc.empty() if successful
    template <typename T>
    Result<PartialNode<T>> decode_partial_node(
        byte_string_view &enc, mpt::NibblesView curr_path,
        NodeIndex const &nodes)
    {
        if (MONAD_UNLIKELY(enc.empty())) {
            return rlp::DecodeError::InputTooShort;
        }

        {
            // Make a copy of enc in case we need to backtrack in the branch
            // case below
            byte_string_view short_node_enc{enc};
            BOOST_OUTCOME_TRY(
                auto key_enc, rlp::parse_metadata(short_node_enc));
            BOOST_OUTCOME_TRY(
                auto val_enc, rlp::parse_metadata(short_node_enc));

            if (short_node_enc.empty()) {
                enc = short_node_enc;
                // Extension/Leaf node
                if (MONAD_UNLIKELY(key_enc.first != rlp::RlpType::String)) {
                    return rlp::DecodeError::TypeUnexpected;
                }

                BOOST_OUTCOME_TRY(
                    auto decoded_pair, mpt::compact_decode(key_enc.second));
                auto const &[decoded_path, is_leaf] = decoded_pair;
                mpt::Nibbles full_path =
                    mpt::concat(curr_path, mpt::NibblesView{decoded_path});

                if (MONAD_UNLIKELY(full_path.nibble_size() > 64)) {
                    return rlp::DecodeError::PathTooLong;
                }

                if (is_leaf) {
                    if (MONAD_UNLIKELY(val_enc.first != rlp::RlpType::String)) {
                        return rlp::DecodeError::TypeUnexpected;
                    }
                    BOOST_OUTCOME_TRY(
                        auto value, T::decode(val_enc.second, nodes));
                    MONAD_DEBUG_ASSERT(val_enc.second.empty());
                    return PartialNode<T>{
                        LeafData<T>{std::move(decoded_path), std::move(value)}};
                }
                else {
                    BOOST_OUTCOME_TRY(
                        auto child,
                        decode_child_ref<T>(
                            val_enc.first,
                            val_enc.second,
                            mpt::NibblesView{full_path},
                            nodes));
                    MONAD_DEBUG_ASSERT(val_enc.second.empty());
                    return PartialNode<T>{ExtensionData<T>{
                        std::move(decoded_path), std::move(child)}};
                }
            }
        }

        // Branch node: re-parse from the beginning since we consumed k and v
        // above
        BranchData<T> branch{};

        if (MONAD_UNLIKELY(curr_path.nibble_size() + 1 > 64)) {
            return rlp::DecodeError::PathTooLong;
        }

        for (unsigned i = 0; i < 16; ++i) {
            BOOST_OUTCOME_TRY(auto child_enc, rlp::parse_metadata(enc));
            mpt::Nibbles child_path =
                mpt::concat(curr_path, static_cast<unsigned char>(i));
            BOOST_OUTCOME_TRY(
                auto child,
                decode_child_ref<T>(
                    child_enc.first,
                    child_enc.second,
                    mpt::NibblesView{child_path},
                    nodes));
            branch.children[i] = std::move(child);
        }
        BOOST_OUTCOME_TRY(auto v_enc, rlp::decode_string(enc));
        if (!v_enc.empty()) {
            BOOST_OUTCOME_TRY(auto value, T::decode(v_enc, nodes));
            MONAD_DEBUG_ASSERT(v_enc.empty());
            branch.value = std::move(value);
        }
        if (MONAD_UNLIKELY(!enc.empty())) {
            return rlp::DecodeError::InputTooLong;
        }
        return PartialNode<T>{std::move(branch)};
    }

    // ensures enc.empty() if successful
    template <typename T>
    Result<ChildRef<T>> decode_child_ref(
        rlp::RlpType ty, byte_string_view &enc, mpt::NibblesView path,
        NodeIndex const &nodes)
    {
        if (ty == rlp::RlpType::List) {
            // Embedded node (inline RLP list). Ethereum requires the *full* RLP
            // encoding of an inline node to be < 32 bytes; since `enc` is the
            // list payload (header already stripped), its size must be <= 30.
            if (MONAD_UNLIKELY(enc.size() > 30)) {
                return rlp::DecodeError::InputTooLong;
            }
            // Manual expansion of BOOST_OUTCOME_TRY to avoid a named
            // PartialNode<T> local that triggers a GCC false-positive
            // -Wmaybe-uninitialized on the unique_ptr inside AccountLeafValue.
            auto node_result_ = decode_partial_node<T>(enc, path, nodes);
            if (MONAD_UNLIKELY(node_result_.has_failure())) {
                return std::move(node_result_).as_failure();
            }
            MONAD_DEBUG_ASSERT(enc.empty());
            return std::make_unique<PartialNode<T>>(
                std::move(node_result_).assume_value());
        }
        else {
            // String: either empty (null slot) or 32-byte hash reference
            if (enc.empty()) {
                return nullptr;
            }
            if (MONAD_UNLIKELY(enc.size() < 32)) {
                return rlp::DecodeError::InputTooShort;
            }
            if (MONAD_UNLIKELY(enc.size() > 32)) {
                return rlp::DecodeError::InputTooLong;
            }
            bytes32_t hash{};
            std::memcpy(hash.bytes, enc.data(), 32);
            enc = enc.substr(32);
            MONAD_DEBUG_ASSERT(enc.empty());
            // NULL_ROOT is the canonical empty-trie hash; represent it as a
            // null pointer so encode/decode are symmetric with
            // AccountLeafValue.
            if (hash == NULL_ROOT) {
                return nullptr;
            }
            auto it = nodes.find(hash);
            if (it == nodes.end()) {
                return std::make_unique<PartialNode<T>>(HashStub{hash});
            }
            // The NodeIndex stores the raw RLP item (list). Strip the list
            // header before passing the payload to decode_partial_node.
            byte_string_view node_enc{it->second};
            BOOST_OUTCOME_TRY(auto payload, rlp::parse_list_metadata(node_enc));
            if (MONAD_UNLIKELY(!node_enc.empty())) {
                return rlp::DecodeError::InputTooLong;
            }
            BOOST_OUTCOME_TRY(
                auto v, decode_partial_node<T>(payload, path, nodes));
            MONAD_DEBUG_ASSERT(payload.empty());
            return std::make_unique<PartialNode<T>>(std::move(v));
        }
    }

    template <typename T>
    byte_string encode_partial_node(PartialNode<T> const &node)
    {
        return std::visit(
            Cases{
                [](LeafData<T> const &leaf) {
                    MONAD_ASSERT(leaf.path.nibble_size() <= 64);
                    unsigned char compact_buf[33];
                    auto compact_sv = mpt::compact_encode(
                        compact_buf,
                        mpt::NibblesView{leaf.path},
                        /*terminating=*/true);
                    return rlp::encode_list2(
                        rlp::encode_string2(compact_sv),
                        rlp::encode_string2(T::encode(leaf.value)));
                },
                [](ExtensionData<T> const &ext) {
                    MONAD_ASSERT(ext.path.nibble_size() <= 64);
                    unsigned char compact_buf[33];
                    auto compact_sv = mpt::compact_encode(
                        compact_buf,
                        mpt::NibblesView{ext.path},
                        /*terminating=*/false);
                    return rlp::encode_list2(
                        rlp::encode_string2(compact_sv),
                        encode_child_ref(ext.child));
                },
                [](BranchData<T> const &branch) {
                    byte_string body;
                    for (unsigned i = 0; i < 16; ++i) {
                        body += encode_child_ref(branch.children[i]);
                    }
                    body += branch.value ? T::encode(*branch.value)
                                         : rlp::EMPTY_STRING;
                    return rlp::encode_list2(body);
                },
                [](HashStub const &) -> byte_string {
                    // HashStub is handled by callers; never arrives here.
                    MONAD_ASSERT(false);
                    return {};
                },
            },
            node.v);
    }

    template <typename T>
    byte_string encode_child_ref(ChildRef<T> const &child)
    {
        if (!child) {
            return rlp::EMPTY_STRING;
        }
        if (auto const *stub = std::get_if<HashStub>(&child->v)) {
            return rlp::encode_string2(byte_string_view{stub->hash.bytes, 32});
        }
        byte_string rlp_bytes = encode_partial_node(*child);
        if (rlp_bytes.size() < 32) {
            return rlp_bytes; // embedded inline
        }
        unsigned char hash[32];
        keccak256(rlp_bytes.data(), rlp_bytes.size(), hash);
        return rlp::encode_string2(byte_string_view{hash, 32});
    }

    /// Walk the trie rooted at `root` following the given nibble key.
    /// Aborts if the lookup hits an unresolved HashStub, and returns
    /// a pointer to the leaf value on success, or nullptr if the key is absent.
    template <typename T>
    T *trie_lookup(ChildRef<T> const &root, mpt::NibblesView remaining)
    {
        PartialNode<T> *node = root.get();
        while (node != nullptr) {
            if (auto *leaf = std::get_if<LeafData<T>>(&node->v)) {
                return (mpt::NibblesView{leaf->path} == remaining)
                           ? &leaf->value
                           : nullptr;
            }
            else if (auto *ext = std::get_if<ExtensionData<T>>(&node->v)) {
                mpt::NibblesView const ext_path{ext->path};
                if (!remaining.starts_with(ext_path)) {
                    return nullptr;
                }
                remaining = remaining.substr(ext_path.nibble_size());
                node = ext->child.get();
            }
            else if (auto *branch = std::get_if<BranchData<T>>(&node->v)) {
                if (remaining.empty()) {
                    return branch->value ? &*branch->value : nullptr;
                }
                unsigned const nibble = remaining.get(0);
                remaining = remaining.substr(1);
                node = branch->children[nibble].get();
            }
            else {
                // HashStub: subtree not present in witness
                MONAD_ASSERT(false);
            }
        }
        return nullptr; // null child — key absent
    }

    unsigned
    common_prefix_length(mpt::NibblesView const a, mpt::NibblesView const b)
    {
        unsigned const n = std::min(a.nibble_size(), b.nibble_size());
        for (unsigned i = 0; i < n; ++i) {
            if (a.get(i) != b.get(i)) {
                return i;
            }
        }
        return n;
    }

    // Insert or update a leaf in the trie when override = true.
    // Get or insert when override = false.
    template <bool override = true, typename T>
    T &trie_get_or_upsert(ChildRef<T> &root, mpt::NibblesView key, T value);

    template <bool override, typename T>
    [[gnu::always_inline]] inline T &trie_get_or_upsert_at_new_branch(
        ChildRef<T> &root, BranchData<T> &&branch, unsigned const common_prefix,
        mpt::NibblesView key, T value)
    {
        T *ret_val{};

        if (common_prefix < key.nibble_size()) {
            ret_val = &trie_get_or_upsert<override>(
                branch.children[key.get(common_prefix)],
                key.substr(common_prefix + 1),
                std::move(value));
        }
        else {
            if constexpr (override) {
                branch.value = std::move(value);
            }
            else {
                if (!branch.value) {
                    branch.value = std::move(value);
                }
            }
        }

        if (common_prefix > 0) {
            root = std::make_unique<PartialNode<T>>(ExtensionData<T>{
                mpt::Nibbles{key.substr(0, common_prefix)},
                std::make_unique<PartialNode<T>>(std::move(branch))});
            // if the value was stored in branch.value, we need to fetch
            // value's pointer after the move
            if (!ret_val) {
                return *(std::get<BranchData<T>>(
                             std::get<ExtensionData<T>>(root->v).child->v)
                             .value);
            }
        }
        else {
            root = std::make_unique<PartialNode<T>>(std::move(branch));
            // if the value was stored in branch.value, we need to fetch
            // value's pointer after the move
            if (!ret_val) {
                return *std::get<BranchData<T>>(root->v).value;
            }
        }
        return *ret_val;
    }

    template <bool override, typename T>
    [[gnu::always_inline]] inline T &trie_get_or_upsert_at_branch(
        BranchData<T> &branch, mpt::NibblesView key, T value)
    {
        if (key.empty()) {
            if constexpr (override) {
                branch.value = std::move(value);
            }
            else {
                if (!branch.value) {
                    branch.value = std::move(value);
                }
            }
            return *branch.value;
        }
        return trie_get_or_upsert<override>(
            branch.children[key.get(0)], key.substr(1), std::move(value));
    }

    template <bool override, typename T>
    T &trie_get_or_upsert(ChildRef<T> &root, mpt::NibblesView key, T value)
    {
        if (!root) {
            root = std::make_unique<PartialNode<T>>(
                LeafData<T>{mpt::Nibbles{key}, std::move(value)});
            return std::get<LeafData<T>>(root->v).value;
        }

        return std::visit(
            Cases{
                [&](LeafData<T> &leaf) -> T & {
                    mpt::NibblesView const leaf_path{leaf.path};
                    if (leaf_path == key) {
                        if constexpr (override) {
                            leaf.value = std::move(value);
                        }
                        return leaf.value;
                    }

                    unsigned const cp = common_prefix_length(leaf_path, key);
                    MONAD_DEBUG_ASSERT(
                        cp < leaf_path.nibble_size() || cp < key.nibble_size());

                    BranchData<T> branch{};

                    if (cp < leaf_path.nibble_size()) {
                        branch.children[leaf_path.get(cp)] =
                            std::make_unique<PartialNode<T>>(LeafData<T>{
                                mpt::Nibbles{leaf_path.substr(cp + 1)},
                                std::move(leaf.value)});
                    }
                    else {
                        branch.value = std::move(leaf.value);
                    }

                    return trie_get_or_upsert_at_new_branch<override>(
                        root, std::move(branch), cp, key, std::move(value));
                },
                [&](ExtensionData<T> &ext) -> T & {
                    mpt::NibblesView const ext_path{ext.path};

                    unsigned const cp = common_prefix_length(ext_path, key);
                    if (cp == ext_path.nibble_size()) {
                        return trie_get_or_upsert<override>(
                            ext.child, key.substr(cp), std::move(value));
                    }

                    BranchData<T> branch{};

                    branch.children[ext_path.get(cp)] =
                        (cp + 1 < ext_path.nibble_size())
                            ? std::make_unique<PartialNode<T>>(ExtensionData<T>{
                                  mpt::Nibbles{ext_path.substr(cp + 1)},
                                  std::move(ext.child)})
                            : std::move(ext.child);

                    return trie_get_or_upsert_at_new_branch<override>(
                        root, std::move(branch), cp, key, std::move(value));
                },
                [&](BranchData<T> &branch) -> T & {
                    return trie_get_or_upsert_at_branch<override>(
                        branch, key, std::move(value));
                },
                [](HashStub &) -> T & {
                    // HashStub — witness incomplete
                    MONAD_ASSERT(false);
                    std::unreachable();
                },
            },
            root->v);
    }

    template <typename Prefix, typename T>
        requires(
            std::same_as<Prefix, unsigned char> ||
            std::same_as<Prefix, mpt::NibblesView>)
    [[gnu::always_inline]] inline std::optional<ChildRef<T>>
    concat_path_maybe(Prefix const prefix, ChildRef<T> &node)
    {
        if (auto *child_leaf = std::get_if<LeafData<T>>(&node->v)) {
            child_leaf->path =
                mpt::concat(prefix, mpt::NibblesView{child_leaf->path});
            return std::move(node);
        }
        else if (auto *child_ext = std::get_if<ExtensionData<T>>(&node->v)) {
            child_ext->path =
                mpt::concat(prefix, mpt::NibblesView{child_ext->path});
            return std::move(node);
        }
        return std::nullopt;
    }

    enum class DeleteResult
    {
        Reset,
        Compressed,
        Unchanged
    };

    /// Delete a leaf from the trie at the given nibble key, applying branch
    /// compression as needed. Returns:
    ///   - Reset:      `root` was reset to null (the node went away).
    ///   - Compressed: `root` was reassigned (path-merge or branch collapsed
    ///                 to a leaf/ext); the node still exists but has changed
    ///                 identity.
    ///   - Unchanged:  no structural change at this level (either the key
    ///                 was absent, or a delete happened deeper but did not
    ///                 propagate a shape change here).
    template <typename T>
    DeleteResult trie_delete(ChildRef<T> &root, mpt::NibblesView key)
    {
        if (!root) {
            return DeleteResult::Unchanged;
        }

        return std::visit(
            Cases{
                [&](LeafData<T> &leaf) -> DeleteResult {
                    if (mpt::NibblesView{leaf.path} == key) {
                        root.reset();
                        return DeleteResult::Reset;
                    }
                    return DeleteResult::Unchanged;
                },
                [&](ExtensionData<T> &ext) -> DeleteResult {
                    mpt::NibblesView const ext_path{ext.path};
                    unsigned const cp = common_prefix_length(ext_path, key);
                    if (cp < ext_path.nibble_size()) {
                        return DeleteResult::Unchanged;
                    }
                    switch (trie_delete(ext.child, key.substr(cp))) {
                    case DeleteResult::Unchanged:
                        return DeleteResult::Unchanged;
                    case DeleteResult::Reset:
                        root.reset();
                        return DeleteResult::Reset;
                    case DeleteResult::Compressed: {
                        // Merge paths if child is now a leaf or
                        // extension
                        auto maybe_compressed = concat_path_maybe(
                            mpt::NibblesView{ext.path}, ext.child);
                        if (maybe_compressed) {
                            root = std::move(*maybe_compressed);
                            return DeleteResult::Compressed;
                        }
                        return DeleteResult::Unchanged;
                    }
                    }
                    std::unreachable();
                },
                [&](BranchData<T> &branch) -> DeleteResult {
                    if (key.empty()) {
                        if (!branch.value) {
                            return DeleteResult::Unchanged;
                        }
                        branch.value.reset();
                    }
                    else if (
                        trie_delete(
                            branch.children[key.get(0)], key.substr(1)) !=
                        DeleteResult::Reset) {
                        // we can exit early as long as we know that the call to
                        // trie_delete didn't result in a reset.
                        // Even if compression occured, the child is still
                        // non-null, hence no compaction will occur
                        return DeleteResult::Unchanged;
                    }

                    unsigned child_count = 0;
                    unsigned single_idx = 0;
                    for (unsigned i = 0; i < 16 && child_count < 2; ++i) {
                        if (branch.children[i]) {
                            ++child_count;
                            single_idx = i;
                        }
                    }
                    bool const has_value = branch.value.has_value();

                    if (child_count == 0 && !has_value) {
                        root.reset();
                        return DeleteResult::Reset;
                    }
                    if (child_count == 0 && has_value) {
                        root = std::make_unique<PartialNode<T>>(LeafData<T>{
                            mpt::Nibbles{}, std::move(*branch.value)});
                        return DeleteResult::Compressed;
                    }
                    if (child_count == 1 && !has_value) {
                        auto &child = branch.children[single_idx];
                        auto const nibble =
                            static_cast<unsigned char>(single_idx);
                        auto maybe_compressed =
                            concat_path_maybe(nibble, child);
                        if (maybe_compressed) {
                            root = std::move(*maybe_compressed);
                        }
                        else {
                            // Branch or HashStub child — wrap in extension
                            mpt::Nibbles nibble_path{1};
                            nibble_path.set(0, nibble);
                            root = std::make_unique<PartialNode<T>>(
                                ExtensionData<T>{
                                    std::move(nibble_path), std::move(child)});
                        }

                        return DeleteResult::Compressed;
                    }
                    return DeleteResult::Unchanged;
                },
                [](HashStub &) -> DeleteResult {
                    // HashStub — witness incomplete
                    MONAD_ASSERT(false);
                    std::unreachable();
                },
            },
            root->v);
    }

} // anonymous namespace

// ensures enc.empty() if successful
Result<AccountLeafValue>
AccountLeafValue::decode(byte_string_view &enc, NodeIndex const &nodes)
{
    bytes32_t storage_root{};
    BOOST_OUTCOME_TRY(Account acct, rlp::decode_account(storage_root, enc));
    if (MONAD_UNLIKELY(!enc.empty())) {
        return rlp::DecodeError::InputTooLong;
    }
    StorageTrie strie;
    if (storage_root != NULL_ROOT) {
        mpt::Nibbles empty_path{};
        byte_string_view storage_root_enc{
            storage_root.bytes, sizeof(storage_root.bytes)};
        BOOST_OUTCOME_TRY(
            strie,
            decode_child_ref<StorageLeafValue>(
                rlp::RlpType::String,
                storage_root_enc,
                mpt::NibblesView{empty_path},
                nodes));
        MONAD_DEBUG_ASSERT(storage_root_enc.empty());
    }

    return AccountLeafValue{.account = acct, .storage = std::move(strie)};
}

byte_string AccountLeafValue::encode(AccountLeafValue const &v)
{
    bytes32_t storage_root;
    if (!v.storage) {
        storage_root = NULL_ROOT;
    }
    else {
        auto const &storage_node = *v.storage;
        if (auto const *stub = std::get_if<HashStub>(&storage_node.v)) {
            storage_root = stub->hash;
        }
        else {
            byte_string rlp_bytes = encode_partial_node(storage_node);
            storage_root = to_bytes(keccak256(
                byte_string_view{rlp_bytes.data(), rlp_bytes.size()}));
        }
    }

    return rlp::encode_account(v.account, storage_root);
}

// ensures enc.empty() if successful
Result<StorageLeafValue>
StorageLeafValue::decode(byte_string_view &enc, NodeIndex const & /*nodes*/)
{
    BOOST_OUTCOME_TRY(auto const raw, rlp::decode_bytes32_compact(enc));
    if (MONAD_UNLIKELY(!enc.empty())) {
        return rlp::DecodeError::InputTooLong;
    }
    return StorageLeafValue{raw};
}

byte_string StorageLeafValue::encode(StorageLeafValue const &v)
{
    return rlp::encode_bytes32_compact(v.value);
}

template <>
Result<PartialTrieDb<NoopAccessTracker>>
PartialTrieDb<NoopAccessTracker>::from_reth_witness(
    bytes32_t const &pre_state_root, byte_string_view encoded_nodes,
    byte_string_view encoded_codes)
{
    NodeIndex node_index;
    {
        while (!encoded_nodes.empty()) {
            BOOST_OUTCOME_TRY(
                auto payload, rlp::parse_string_metadata(encoded_nodes));
            bytes32_t key = to_bytes(keccak256(payload));
            node_index.emplace(
                key, byte_string{payload.data(), payload.size()});
        }
    }

    CodeIndex code_index;
    {
        while (!encoded_codes.empty()) {
            BOOST_OUTCOME_TRY(
                auto bytes, rlp::parse_string_metadata(encoded_codes));
            bytes32_t key = to_bytes(keccak256(bytes));
            code_index.emplace(
                key,
                vm::make_shared_intercode(
                    std::span<uint8_t const>{bytes.data(), bytes.size()}));
        }
    }

    AccountTrie root_node;
    {
        mpt::Nibbles empty_path{};
        byte_string_view pre_state_root_enc{
            pre_state_root.bytes, sizeof(pre_state_root.bytes)};
        BOOST_OUTCOME_TRY(
            root_node,
            decode_child_ref<AccountLeafValue>(
                rlp::RlpType::String,
                pre_state_root_enc,
                mpt::NibblesView{empty_path},
                node_index));
        MONAD_DEBUG_ASSERT(pre_state_root_enc.empty());
    }

    // Shared singleton referenced by every PartialTrieDb<NoopAccessTracker>:
    // the type is stateless and no call site ever dereferences it (all
    // tracker operations are elided at compile time when Tracker::enabled
    // is false). Static so the reference outlives this function.
    static NoopAccessTracker noop_access_tracker{};
    return PartialTrieDb<NoopAccessTracker>{
        noop_access_tracker, std::move(root_node), std::move(code_index)};
}

template <typename Tracker>
template <LeafValue V>
V *PartialTrieDb<Tracker>::trie_lookup(
    ChildRef<V> const &root, mpt::NibblesView remaining) const
{
    PartialNode<V> *node = root.get();
    while (node != nullptr) {
        if constexpr (Tracker::enabled) {
            tracker_.mark_accessed(static_cast<void const *>(node));
        }
        if (auto *leaf = std::get_if<LeafData<V>>(&node->v)) {
            return (mpt::NibblesView{leaf->path} == remaining) ? &leaf->value
                                                               : nullptr;
        }
        else if (auto *ext = std::get_if<ExtensionData<V>>(&node->v)) {
            mpt::NibblesView const ext_path{ext->path};
            if (!remaining.starts_with(ext_path)) {
                return nullptr;
            }
            remaining = remaining.substr(ext_path.nibble_size());
            node = ext->child.get();
        }
        else if (auto *branch = std::get_if<BranchData<V>>(&node->v)) {
            if (remaining.empty()) {
                return branch->value ? &*branch->value : nullptr;
            }
            unsigned const nibble = remaining.get(0);
            remaining = remaining.substr(1);
            node = branch->children[nibble].get();
        }
        else {
            // HashStub: subtree not present in witness
            MONAD_ASSERT(false);
        }
    }
    return nullptr; // null child — key absent
}

template <typename Tracker>
std::optional<Account> PartialTrieDb<Tracker>::read_account(Address const &addr)
{
    auto const key_hash = keccak256(addr.bytes);
    auto const result = trie_lookup(root_, mpt::NibblesView{key_hash});
    if (!result) {
        return std::nullopt;
    }
    return result->account;
}

template <typename Tracker>
bytes32_t PartialTrieDb<Tracker>::read_storage(
    Address const &addr, Incarnation, bytes32_t const &slot)
{
    auto const acct_hash = keccak256(addr.bytes);
    auto const acct_result = trie_lookup(root_, mpt::NibblesView{acct_hash});
    if (!acct_result || !acct_result->storage) {
        return {};
    }
    auto const slot_hash = keccak256(slot.bytes);
    auto const val_result =
        trie_lookup(acct_result->storage, mpt::NibblesView{slot_hash});
    return !val_result ? bytes32_t{} : val_result->value;
}

template <typename Tracker>
vm::SharedIntercode
PartialTrieDb<Tracker>::read_code(bytes32_t const &code_hash)
{
    auto it = codes_.find(code_hash);
    if (it == codes_.end()) {
        return vm::make_shared_intercode({});
    }
    if constexpr (Tracker::enabled) {
        if (code_hash != NULL_HASH) {
            tracker_.mark_code(it->second);
        }
    }
    return it->second;
}

template <typename Tracker>
BlockHeader PartialTrieDb<Tracker>::read_eth_header()
{
    return last_committed_header_;
}

template <typename Tracker>
bytes32_t PartialTrieDb<Tracker>::state_root()
{
    if (!root_) {
        return NULL_ROOT;
    }
    if (auto const *stub = std::get_if<HashStub>(&root_->v)) {
        return stub->hash;
    }
    byte_string rlp_bytes = encode_partial_node(*root_);
    return to_bytes(
        keccak256(byte_string_view{rlp_bytes.data(), rlp_bytes.size()}));
}

template <typename Tracker>
bytes32_t PartialTrieDb<Tracker>::receipts_root()
{
    return last_committed_header_.receipts_root;
}

template <typename Tracker>
bytes32_t PartialTrieDb<Tracker>::transactions_root()
{
    return last_committed_header_.transactions_root;
}

template <typename Tracker>
std::optional<bytes32_t> PartialTrieDb<Tracker>::withdrawals_root()
{
    return last_committed_header_.withdrawals_root;
}

template <typename Tracker>
uint64_t PartialTrieDb<Tracker>::get_block_number() const
{
    return block_number_;
}

template <typename Tracker>
void PartialTrieDb<Tracker>::set_block_and_prefix(
    uint64_t block_number, bytes32_t const &)
{
    block_number_ = block_number;
}

template <typename Tracker>
void PartialTrieDb<Tracker>::commit(
    bytes32_t const &, CommitBuilder &builder, BlockHeader const &header,
    StateDeltas const &deltas,
    std::function<void(BlockHeader &)> populate_header_fn)
{
    block_number_ = header.number;

    // Pull codes out of the builder's update list. TrieDb persists
    // these under CODE_NIBBLE via db_.upsert; PartialTrieDb has no
    // underlying mpt::Db, so we re-materialize SharedIntercodes into
    // codes_ where read_code can find them.
    // build(prefix) wraps the top-level updates_ under a single Update
    // whose .next is the real list, so descend one level first.
    auto const updates = builder.build(mpt::NibblesView{});
    for (auto const &top : updates) {
        for (auto const &u : top.next) {
            if (u.key != mpt::NibblesView{code_nibbles}) {
                continue;
            }
            for (auto const &cu : u.next) {
                MONAD_ASSERT(cu.value.has_value());
                auto const &bytes = *cu.value;
                bytes32_t hash;
                std::memcpy(hash.bytes, cu.key.data(), 32);
                codes_.try_emplace(
                    hash,
                    vm::make_shared_intercode(
                        std::span<uint8_t const>{bytes.data(), bytes.size()}));
            }
        }
    }

    // Pass 1: inserts and updates (accounts that exist in post-state)
    for (auto const &[addr, delta] : deltas) {
        auto const &new_account = delta.account.second;
        if (!new_account) {
            continue;
        }

        auto const acct_key = keccak256(addr.bytes);

        auto &existing = trie_get_or_upsert<false>(
            root_, mpt::NibblesView{acct_key}, AccountLeafValue{});

        // Incarnation bump: the account was destroyed and recreated in
        // this block (CREATE2/SELFDESTRUCT/CREATE2 patterns). The old
        // storage trie must be wiped before the new slot deltas apply
        if (delta.account.first.has_value() &&
            delta.account.first->incarnation != new_account->incarnation) {
            existing.storage.reset();
        }

        existing.account = *new_account;

        auto &storage = existing.storage;

        // Apply storage deltas: upserts first, then deletions
        for (auto const &[slot, sdelta] : delta.storage) {
            if (sdelta.second != bytes32_t{}) {
                auto const slot_key = keccak256(slot.bytes);
                trie_get_or_upsert(
                    storage,
                    mpt::NibblesView{slot_key},
                    StorageLeafValue{sdelta.second});
            }
        }
        for (auto const &[slot, sdelta] : delta.storage) {
            if (sdelta.second == bytes32_t{} && sdelta.first != bytes32_t{}) {
                auto const slot_key = keccak256(slot.bytes);
                trie_delete(storage, mpt::NibblesView{slot_key});
            }
        }
    }

    // Pass 2: deletions (accounts removed in post-state)
    for (auto const &[addr, delta] : deltas) {
        if (delta.account.second) {
            continue;
        }
        if (!delta.account.first) {
            continue;
        }
        auto const acct_key = keccak256(addr.bytes);
        trie_delete(root_, mpt::NibblesView{acct_key});
    }

    last_committed_header_ = header;
    MONAD_ASSERT(populate_header_fn);
    populate_header_fn(last_committed_header_);
}

// Pre-pass for the delete set: walk the delete path and, at every branch
// whose target child is fully drained, call tracker_.mark_deleted_child to
// accumulate the child drainage into `deleted_siblings`. Returns true iff
// the subtree rooted at `root` becomes *empty* (null) after the delete —
// not merely compressed. Compression (case A: single surviving child,
// case B: value-only) reshapes the child but leaves the parent's slot
// alive, so drainage only propagates upward when the child truly empties.
//
// Siblings are NOT marked here. A separate post-pass iterates the
// accumulated `deleted_siblings` entries and, for every branch whose final
// alive-pointer array has a single non-null entry, marks that survivor
// (filtered to leaf/extension — branch/stub survivors are wrapped in an
// extension by trie_delete using just the hash).
template <typename Tracker>
template <LeafValue V>
bool PartialTrieDb<Tracker>::mark_deletion_siblings(
    ChildRef<V> const &root, mpt::NibblesView key) const
    requires(Tracker::enabled)
{
    if (!root) {
        return false;
    }
    auto const &node = *root;

    if (auto const *leaf = std::get_if<LeafData<V>>(&node.v)) {
        return mpt::NibblesView{leaf->path} == key;
    }
    if (auto const *ext = std::get_if<ExtensionData<V>>(&node.v)) {
        mpt::NibblesView const ext_path{ext->path};
        if (!key.starts_with(ext_path)) {
            return false;
        }
        // An extension disappears iff its child does.
        return mark_deletion_siblings(
            ext->child, key.substr(ext_path.nibble_size()));
    }
    if (auto const *branch = std::get_if<BranchData<V>>(&node.v)) {
        if (key.empty()) {
            // setting idx = 16 marks the branch.value as being deleted
            tracker_.mark_branch_deleted_child(node, 16);
            return tracker_.is_branch_empty(static_cast<void const *>(&node));
        }

        unsigned const nibble = key.get(0);
        if (!mark_deletion_siblings(branch->children[nibble], key.substr(1))) {
            return false;
        }
        // Child at `nibble` is fully deleted. Record
        // it so the post-pass can detect compression against the cumulative
        // deletes from every block delete that visits this branch.
        tracker_.mark_branch_deleted_child(node, nibble);
        // Only propagate delete upward in this call if this branch is now fully
        // empty.
        return tracker_.is_branch_empty(static_cast<void const *>(&node));
    }

    // HashStub: shouldn't be reachable (trie_delete asserts).
    MONAD_ASSERT(false);
}

// Post-order traversal: encode accessed nodes, append their RLPs to `nodes`,
// and return the child-ref encoding (inline RLP if <32 bytes, else 32-byte
// hash reference). Unaccessed subtrees fall back to encode_child_ref. Each
// node is visited exactly once via its parent, so no dedup is required.
template <typename Tracker>
template <LeafValue V>
byte_string PartialTrieDb<Tracker>::collect_accessed_nodes(
    ChildRef<V> const &child, std::vector<byte_string> &nodes) const
    requires(Tracker::enabled)
{
    if (!child) {
        return rlp::EMPTY_STRING;
    }
    if (auto const *stub = std::get_if<HashStub>(&child->v)) {
        return rlp::encode_string2(byte_string_view{stub->hash.bytes, 32});
    }
    if (!tracker_.was_accessed(static_cast<void const *>(child.get()))) {
        return encode_child_ref(child);
    }

    byte_string rlp_bytes = std::visit(
        Cases{
            [&](LeafData<V> const &leaf) -> byte_string {
                if constexpr (std::is_same_v<V, AccountLeafValue>) {
                    if (leaf.value.storage) {
                        (void)collect_accessed_nodes(leaf.value.storage, nodes);
                    }
                    // Empty storage (storage_root == NULL_ROOT) needs no
                    // preimage: decode_child_ref short-circuits on
                    // NULL_ROOT before looking it up in the NodeIndex.
                }
                MONAD_ASSERT(leaf.path.nibble_size() <= 64);
                unsigned char compact_buf[33];
                auto compact_sv = mpt::compact_encode(
                    compact_buf,
                    mpt::NibblesView{leaf.path},
                    /*terminating=*/true);
                return rlp::encode_list2(
                    rlp::encode_string2(compact_sv),
                    rlp::encode_string2(V::encode(leaf.value)));
            },
            [&](ExtensionData<V> const &ext) -> byte_string {
                MONAD_ASSERT(ext.path.nibble_size() <= 64);
                unsigned char compact_buf[33];
                auto compact_sv = mpt::compact_encode(
                    compact_buf,
                    mpt::NibblesView{ext.path},
                    /*terminating=*/false);
                return rlp::encode_list2(
                    rlp::encode_string2(compact_sv),
                    collect_accessed_nodes(ext.child, nodes));
            },
            [&](BranchData<V> const &branch) -> byte_string {
                byte_string body;
                for (unsigned i = 0; i < 16; ++i) {
                    body += collect_accessed_nodes(branch.children[i], nodes);
                }
                body +=
                    branch.value ? V::encode(*branch.value) : rlp::EMPTY_STRING;
                return rlp::encode_list2(body);
            },
            [&](HashStub const &) -> byte_string {
                MONAD_ASSERT(false);
                return {};
            },
        },
        child->v);

    if (rlp_bytes.size() < 32) {
        return rlp_bytes; // inlined in parent; no separate entry
    }
    bytes32_t hash;
    keccak256(rlp_bytes.data(), rlp_bytes.size(), hash.bytes);
    nodes.push_back(std::move(rlp_bytes));
    return rlp::encode_string2(byte_string_view{hash.bytes, 32});
}

template <typename Tracker>
WitnessData
PartialTrieDb<Tracker>::collect_witness(StateDeltas const &deltas) const
    requires(Tracker::enabled)
{
    WitnessData wd;

    // Mark every delta key as accessed. Reads during execution are
    // already tracked by trie_lookup; this adds write-only paths that were
    // never read.
    for (auto const &[addr, delta] : deltas) {
        auto const acct_key = keccak256(addr.bytes);
        auto const acct_result = trie_lookup(root_, mpt::NibblesView{acct_key});
        if (!!acct_result) {
            auto const &storage = acct_result->storage;
            for (auto const &[slot, _] : delta.storage) {
                auto const slot_key = keccak256(slot.bytes);
                (void)trie_lookup(storage, mpt::NibblesView{slot_key});
            }
        }
    }

    // Codes come from the tracker's code set, populated by `read_code`
    // during block execution. Only actual bytecode loads count,
    // so EXTCODESIZE/EXTCODEHASH (which read Account.code_hash without
    // loading) are excluded.
    wd.codes.assign(
        tracker_.loaded_codes().begin(), tracker_.loaded_codes().end());

    // For each deletion, call mark_deletion_siblings to track the sibling
    // (if any) that will be promoted by branch compression.
    for (auto const &[addr, delta] : deltas) {
        auto const acct_key = keccak256(addr.bytes);
        if (!delta.account.second && delta.account.first) {
            (void)mark_deletion_siblings(root_, mpt::NibblesView{acct_key});
        }
        auto const acct_result = trie_lookup(root_, mpt::NibblesView{acct_key});
        if (!!acct_result) {
            auto const &storage = acct_result->storage;
            for (auto const &[slot, sdelta] : delta.storage) {
                if (sdelta.first != bytes32_t{} &&
                    sdelta.second == bytes32_t{}) {
                    auto const slot_key = keccak256(slot.bytes);
                    (void)mark_deletion_siblings(
                        storage, mpt::NibblesView{slot_key});
                }
            }
        }
    }

    // We touch any children which are the sole survivors in a branch
    // after all deletes have been recorded.
    // The witness consumer will need the actual child, instead of a hash stub,
    // to perform the branch extension/leaf promotion during witness
    // re-exceution. Empty (zero live) or value-only (value is encoded inline in
    // the branch's own RLP) cases need no extra marking here.
    for (auto const &[branch_ptr, access] : tracker_.deleted_siblings) {
        if (tracker_.will_branch_compress(branch_ptr)) {
            for (auto const *c : access.children) {
                if (c) {
                    tracker_.mark_accessed(c);
                    break;
                }
            }
        }
    }

    // Post-order traversal appends RLPs of accessed nodes to
    // wd.nodes. Each node is visited exactly once via its parent, so no
    // dedup is needed.
    (void)collect_accessed_nodes(root_, wd.nodes);

    return wd;
}

template class PartialTrieDb<AccessTracker>;
template class PartialTrieDb<NoopAccessTracker>;

MONAD_NAMESPACE_END
