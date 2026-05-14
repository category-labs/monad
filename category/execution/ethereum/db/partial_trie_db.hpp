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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/partial_node.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <functional>
#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

struct StorageLeafValue
{
    bytes32_t value;

    static Result<StorageLeafValue>
    decode(byte_string_view &enc, NodeIndex const & /*nodes*/);

    static byte_string encode(StorageLeafValue const &v);
};

using StorageTrie = ChildRef<StorageLeafValue>;

struct AccountLeafValue
{
    Account account;
    StorageTrie
        storage{}; ///< per-account storage MPT, embedded directly in the leaf

    static Result<AccountLeafValue>
    decode(byte_string_view &enc, NodeIndex const &nodes);

    static byte_string encode(AccountLeafValue const &v);
};

using AccountTrie = ChildRef<AccountLeafValue>;

using CodeIndex = ankerl::unordered_dense::map<bytes32_t, vm::SharedIntercode>;

// ---------------------------------------------------------------------------
// Public operations over an AccountTrie.
//
// These wrap the template-heavy trie machinery (currently kept in the .cpp's
// anonymous namespace) so consumers — PartialTrieDb itself, and HashCache —
// can apply block deltas and re-hash an in-memory sparse account trie without
// each consumer reimplementing the trie ops.
// ---------------------------------------------------------------------------

/// Apply block-wide state deltas to the in-place account trie:
/// account upserts and deletes; per-account storage upserts and deletes;
/// reset the per-account storage trie on an incarnation bump.
/// Requires all paths the deltas touch to be resolved (no HashStub on path).
void apply_state_deltas_to_trie(AccountTrie &root, StateDeltas const &deltas);

/// Compute the Ethereum-canonical state root of the (sparse) account trie
/// by walking it, RLP-encoding each node, and keccak-hashing. No disk I/O.
/// If `root` is null, returns NULL_ROOT. Aborts if the walk hits a HashStub
/// (the caller is responsible for resolving any path that might be hashed).
bytes32_t compute_account_state_root(AccountTrie const &root);

// ---------------------------------------------------------------------------
// PartialTrieDb
// ---------------------------------------------------------------------------

/// A sparse Ethereum account + storage MPT that implements the Db interface.
///
/// Built from a Reth witness bundle; serves as a drop-in replacement for
/// TrieDb during zkVM STF proving. The trie IS the pre-state — there are no
/// separate account or storage vectors.
class PartialTrieDb final : public Db
{
    AccountTrie root_;
    CodeIndex codes_;
    uint64_t block_number_{0};
    BlockHeader last_committed_header_{};

    PartialTrieDb(AccountTrie root, CodeIndex codes)
        : root_{std::move(root)}
        , codes_{std::move(codes)}
    {
    }

public:
    PartialTrieDb() = delete;

    static Result<PartialTrieDb> from_witness(
        bytes32_t const &pre_state_root, byte_string_view encoded_nodes,
        byte_string_view encoded_codes);

    std::optional<Account> read_account(Address const &) override;

    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &key) override;

    vm::SharedIntercode read_code(bytes32_t const &code_hash) override;

    BlockHeader read_eth_header() override;

    bytes32_t state_root() override;
    bytes32_t receipts_root() override;
    bytes32_t transactions_root() override;
    std::optional<bytes32_t> withdrawals_root() override;

    uint64_t get_block_number() const override;

    void set_block_and_prefix(
        uint64_t block_number,
        bytes32_t const &block_id = bytes32_t{}) override;

    void commit(
        bytes32_t const &block_id, CommitBuilder &, BlockHeader const &,
        std::unique_ptr<StateDeltas>,
        std::function<void(BlockHeader &)>) override;

    // No-op overrides for operations that are irrelevant in the witness
    // context.
    void finalize(uint64_t, bytes32_t const &) override {}

    void update_verified_block(uint64_t) override {}

    void update_voted_metadata(uint64_t, bytes32_t const &) override {}

    void update_proposed_metadata(uint64_t, bytes32_t const &) override {}
};

MONAD_NAMESPACE_END
