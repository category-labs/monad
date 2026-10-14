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

// Generate witnesses from genesis and host-executed signed blocks. TrieDb
// computes expected roots; the guest recomputes them with OffsetTrie from the
// witness, providing an independent trie implementation.

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/execute_message.hpp>
#include <category/mpt/db.hpp>

#include <cstdint>
#include <functional>
#include <memory>
#include <vector>

MONAD_NAMESPACE_BEGIN

class State;

namespace corpus
{
    class GenesisSink;

#ifdef MONAD_ZKVM_L2
    /// An L2 chain starts where a chain starts. It has no fork schedule -- its
    /// revision is a constant compiled into the guest -- so no number decides
    /// its rules, and its genesis is block 0.
    inline constexpr uint64_t GENESIS_NUMBER = 0;
#else
    /// Synthetic mainnet height in the Paris window: no withdrawals,
    /// requests_hash or blob fields are needed for the Ethereum guest.
    inline constexpr uint64_t GENESIS_NUMBER = 15'537'394;
#endif
    /// Below SHANGHAI_ACTIVATION_TIMESTAMP (1'681'338'455), and every block
    /// steps by 12s, so a corpus would have to run past 1.5 million blocks to
    /// leave the window.
    inline constexpr uint64_t GENESIS_TIMESTAMP = 1'663'224'179;
    inline constexpr uint64_t BLOCK_TIME = 12;
    inline constexpr uint64_t GAS_LIMIT = 30'000'000;

    /// The id a block is committed and finalized under. Not the number
    /// itself: TrieDb refuses the zero id, and an L2 genesis is block 0. The
    /// id never reaches a hash, so it changes nothing a witness carries.
    inline bytes32_t commit_id(uint64_t const number)
    {
        return bytes32_t{number + 1};
    }

    /// How far back a witness's ancestor headers, field [3], reach.
    enum class Ancestors
    {
        /// Include hashes from the oldest BLOCKHASH read through the parent;
        /// use the parent alone if none were read. Missing required hashes
        /// must abort guest execution.
        Reached,
        /// Every ancestor the block hash buffer can serve, up to its 256: the
        /// shape a mainnet witness has.
        All,
    };

#ifdef MONAD_ZKVM_L2
    /// A block that reads no hash would otherwise carry, and the guest hash
    /// and decode, 256 headers it never uses.
    inline constexpr Ancestors DEFAULT_ANCESTORS = Ancestors::Reached;
#else
    /// The mainnet guest's corpora keep the shape of a mainnet witness.
    inline constexpr Ancestors DEFAULT_ANCESTORS = Ancestors::All;
#endif

    /// One block's worth of input. `keys[i]` signs `txs[i]`; the builder fills
    /// each nonce from the sender's account and signs last, because the nonce
    /// is inside the signing preimage.

    /// Domain transfers need intrinsic gas plus the spoke access-check
    /// stipend, even for an EOA recipient. A 21,000-gas transfer would revert
    /// without reaching the recipient.
#ifdef MONAD_ZKVM_L2
    inline constexpr uint64_t TRANSFER_GAS =
        21'000 + static_cast<uint64_t>(DOMAIN_ACCESS_GAS_STIPEND);
#else
    inline constexpr uint64_t TRANSFER_GAS = 21'000;
#endif

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
        bytes32_t domain_anchor{};
        /// L2 only: the parent hash the guest publishes for chaining.
        bytes32_t parent_hash{};
        /// L2 only: how many leaves were encrypted.
        size_t encrypted_leaves{0};
        /// Expected L2 state commitment and sequencing digest, independently
        /// derived by the corpus for comparison with guest output.
        bytes32_t pre_state_commitment{};
        bytes32_t state_commitment{};
        bytes32_t sequencing_anchor{};
    };

    class CorpusBuilder
    {
    public:
        /// Seed a State with accounts, code and storage. sk is used only in
        /// L2 builds and must match the configured operator key; the
        /// constructor rejects a mismatch before generating any blocks.
        CorpusBuilder(
            std::function<void(State &)> const &seed, bytes32_t const &sk = {},
            bytes32_t const &salt_secret = {});

        /// Bulk genesis through GenesisSink; see genesis_bulk.hpp. gas_limit
        /// is constant across the chain and configurable for large workloads.
        CorpusBuilder(
            std::function<void(GenesisSink &)> const &seed,
            size_t chunk_accounts = 100'000, uint64_t gas_limit = GAS_LIMIT,
            bytes32_t const &sk = {}, bytes32_t const &salt_secret = {});

        ~CorpusBuilder();

        CorpusBuilder(CorpusBuilder const &) = delete;
        CorpusBuilder &operator=(CorpusBuilder const &) = delete;

        /// Execute one block and emit its witness. Throws nothing; aborts on
        /// an execution error, since a corpus block that does not execute is a
        /// bug in the scenario and there is no recovery worth writing.
        Emitted add_block(BlockSpec spec);

        /// The address a CREATE from `deployer` at its current nonce will take.
        Address next_contract_address(Address const &deployer) const;

        /// The per-block state blinder this builder will put in a header's
        /// extra_data. Exposed so a test can check the guest agrees.

        uint64_t next_number() const
        {
            return next_number_;
        }

        /// How far back the next witnesses' field [3] reaches.
        void set_ancestors(Ancestors const a)
        {
            ancestors_ = a;
        }

        TrieDb &db()
        {
            return tdb_;
        }

    private:
        /// Aborts unless `sk_` is the secret behind the compiled
        /// MONAD_ZKVM_L2_OPERATOR_PK_X. No-op off the L2 arm.
        void check_operator_key() const;
        /// Records a sealed genesis header as the chain's first ancestor.
        void seal_genesis(BlockHeader const &);

        struct Impl;
        std::unique_ptr<Impl> impl_;
        mpt::Db mdb_;
        TrieDb tdb_;
        uint64_t gas_limit_{GAS_LIMIT};
        uint64_t next_number_{GENESIS_NUMBER + 1};
        /// Retain sealed headers oldest first for field [3]; the parent must
        /// carry the pre-state root used by the witness.
        std::vector<BlockHeader> sealed_;
        /// Filled as blocks are sealed. Not init_block_hash_buffer_from_triedb,
        /// which asserts is_on_disk() -- and this db is in memory.
        BlockHashBufferFinalized block_hashes_;
        Ancestors ancestors_{DEFAULT_ANCESTORS};
        bytes32_t sk_{};
        bytes32_t salt_secret_{};
    };
}

MONAD_NAMESPACE_END
