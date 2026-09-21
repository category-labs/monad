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

// Builds a corpus of execution witnesses from nothing: a genesis state, blocks
// of signed transactions, executed on the host, each emitted as the witness
// the zkVM guest consumes.
//
// The point is an oracle that is not circular. This side computes the roots
// with TrieDb, the node's own backend; the guest recomputes them with
// OffsetTrie from the blob. Two implementations of the same trie, so their
// agreement says something.

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/mpt/db.hpp>

#include <cstdint>
#include <functional>
#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

namespace corpus
{
    /// The synthetic chain starts here, and the number is load-bearing.
    ///
    /// The non-L2 guest instantiates EthereumMainnet, whose schedule picks the
    /// revision from the block number and then the timestamp. Paris is the one
    /// window with no withdrawals, no requests_hash and no blob fields -- the
    /// exact shape the L2 guest accepts with no lever -- so a corpus generated
    /// here needs none of the scaffolding the rewritten-mainnet corpus did.
    inline constexpr uint64_t GENESIS_NUMBER = 15'537'394;
    /// Below SHANGHAI_ACTIVATION_TIMESTAMP (1'681'338'455), and every block
    /// steps by 12s, so a corpus would have to run past 1.5 million blocks to
    /// leave the window.
    inline constexpr uint64_t GENESIS_TIMESTAMP = 1'663'224'179;
    inline constexpr uint64_t BLOCK_TIME = 12;
    inline constexpr uint64_t GAS_LIMIT = 30'000'000;

    /// One block's worth of input. `keys[i]` signs `txs[i]`; the builder fills
    /// each nonce from the sender's account and signs last, because the nonce
    /// is inside the signing preimage.
    struct BlockSpec
    {
        std::vector<Transaction> txs;
        std::vector<bytes32_t> keys;
        Address beneficiary{};
    };

    struct Emitted
    {
        byte_string witness;
        bytes32_t pre_root;
        bytes32_t post_root;
        bytes32_t block_hash;
        BlockHeader header;
        std::vector<Receipt> receipts;
        /// L2 only, and zero when the block recorded no namespace message.
        bytes32_t namespace_anchor{};
        /// L2 only: how many leaves were encrypted.
        size_t encrypted_leaves{0};
    };

    class CorpusBuilder
    {
    public:
        /// `seed` is handed a State to populate with create_contract /
        /// set_code / add_to_balance / set_nonce / set_storage, which is the
        /// route json_state.cpp takes. Not GenesisState: its "wei_balance"
        /// JSON schema, its concrete TrieDb& and its hardcoded block id are
        /// three frictions for no gain when the caller is C++ to begin with.
        /// `sk` is the operator secret, used only in an L2 tree. It must
        /// match the compiled MONAD_ZKVM_L2_OPERATOR_PK_X or the constructor
        /// aborts -- the same check the guest makes on the witness field, made
        /// here so a misconfigured corpus fails at the start rather than one
        /// leaf at a time inside the guest.
        CorpusBuilder(
            std::function<void(State &)> const &seed, bytes32_t const &sk = {});
        ~CorpusBuilder();

        CorpusBuilder(CorpusBuilder const &) = delete;
        CorpusBuilder &operator=(CorpusBuilder const &) = delete;

        /// Execute one block and emit its witness. Throws nothing; aborts on
        /// an execution error, since a corpus block that does not execute is a
        /// bug in the scenario and there is no recovery worth writing.
        Emitted add_block(BlockSpec spec);

        /// The address a CREATE from `deployer` at its current nonce will take.
        Address next_contract_address(Address const &deployer) const;

        uint64_t next_number() const
        {
            return next_number_;
        }

        TrieDb &db()
        {
            return tdb_;
        }

    private:
        struct Impl;
        std::unique_ptr<Impl> impl_;
        mpt::Db mdb_;
        TrieDb tdb_;
        uint64_t next_number_{GENESIS_NUMBER + 1};
        /// Sealed headers, oldest first, for witness field [3]. Kept as the
        /// commit sealed them rather than rebuilt: field [3]'s newest entry
        /// must carry the pre-state root the blob was generated against, and
        /// a reconstructed header is exactly how that stops being true.
        std::vector<BlockHeader> sealed_;
        /// Filled as blocks are sealed. Not init_block_hash_buffer_from_triedb,
        /// which asserts is_on_disk() -- and this db is in memory.
        BlockHashBufferFinalized block_hashes_;
        bytes32_t sk_{};
    };
}

MONAD_NAMESPACE_END
