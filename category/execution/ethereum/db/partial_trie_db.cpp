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

Result<PartialTrieDb> PartialTrieDb::from_reth_witness(
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

    return PartialTrieDb{std::move(root_node), std::move(code_index)};
}

std::optional<Account> PartialTrieDb::read_account(Address const &)
{
    return std::nullopt;
}

bytes32_t
PartialTrieDb::read_storage(Address const &, Incarnation, bytes32_t const &)
{
    return {};
}

vm::SharedIntercode PartialTrieDb::read_code(bytes32_t const &code_hash)
{
    auto it = codes_.find(code_hash);
    if (it == codes_.end()) {
        return vm::make_shared_intercode({});
    }
    return it->second;
}

BlockHeader PartialTrieDb::read_eth_header()
{
    return last_committed_header_;
}

bytes32_t PartialTrieDb::state_root()
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

bytes32_t PartialTrieDb::receipts_root()
{
    return receipts_root_;
}

bytes32_t PartialTrieDb::transactions_root()
{
    return transactions_root_;
}

std::optional<bytes32_t> PartialTrieDb::withdrawals_root()
{
    return withdrawals_root_;
}

uint64_t PartialTrieDb::get_block_number() const
{
    return block_number_;
}

void PartialTrieDb::set_block_and_prefix(
    uint64_t block_number, bytes32_t const &)
{
    block_number_ = block_number;
}

void PartialTrieDb::commit(
    bytes32_t const &, CommitBuilder &, BlockHeader const &,
    StateDeltas const &, std::function<void(BlockHeader &)>)
{
}

MONAD_NAMESPACE_END
