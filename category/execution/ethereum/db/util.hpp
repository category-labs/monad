// Copyright (C) 2025 Category Labs, Inc.
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
#include <category/core/blake3.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/db/partitioned_layout.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/config.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/state_machine.hpp>

#include <nlohmann/json_fwd.hpp>

#include <algorithm>
#include <filesystem>
#include <functional>
#include <istream>

MONAD_MPT_NAMESPACE_BEGIN

struct Compute;
class Db;
class RODb;

MONAD_MPT_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct MachineBase : public mpt::StateMachine
{
    // symbols in a keccak256 / bytes32 key (64 for 4-bit, 52 for 5-bit)
    static constexpr uint64_t KEY_NIBBLES =
        mpt::nibbles_for_bytes(sizeof(bytes32_t));
    static constexpr uint64_t TABLE_PREFIX_LEN = 1;
    static constexpr uint64_t TOP_NIBBLE_PREFIX_LEN = 1;
    static constexpr uint64_t FINALIZED_PREFIX_LEN =
        TOP_NIBBLE_PREFIX_LEN + TABLE_PREFIX_LEN;
    static constexpr uint64_t PROPOSAL_PREFIX_LEN =
        TOP_NIBBLE_PREFIX_LEN +
        KEY_NIBBLES /* use block_id as proposal prefix */ + TABLE_PREFIX_LEN;

    enum class TrieType : uint8_t
    {
        Undefined,
        Finalized,
        Proposal
    };

    // Order matches nibble values: TableType(nibble + 1)
    enum class TableType : uint8_t
    {
        Prefix,
        State,
        Code,
        Receipt,
        Transaction,
        BlockHeader,
        Withdrawal,
        Ommer,
        TxHash,
        BlockHash,
        CallFrame,
    };

    uint8_t depth{0};
    TrieType trie_section{TrieType::Undefined};
    TableType table{TableType::Prefix};

    virtual mpt::Compute &get_compute() const override;
    virtual void down(unsigned char nibble) override;
    virtual void down(mpt::NibblesView path) override;
    virtual void up(size_t n) override;
    virtual bool is_variable_length() const override;
    constexpr uint8_t prefix_len() const;

    // Deepest leaf in the state table: account hash + storage hash in the
    // nested layout, a storage zone key in the partitioned layout.
    static constexpr uint64_t MAX_STATE_KEY_NIBBLES =
        std::max<uint64_t>(2 * KEY_NIBBLES, partitioned::STORAGE_KEY_NIBBLES);

    constexpr uint8_t max_depth(uint8_t const prefix_length) const
    {
        return static_cast<uint8_t>(prefix_length + MAX_STATE_KEY_NIBBLES);
    }

protected:
    // Per-subclass hooks that select the compute used for storage leaves and
    // the storage root. The default returns the slot-based computes.
    virtual mpt::Compute &storage_compute() const;
    virtual mpt::Compute &storage_root_compute() const;
};

static_assert(sizeof(MachineBase) == 16);
static_assert(alignof(MachineBase) == 8);

struct InMemoryMachine : public MachineBase
{
    virtual mpt::state_machine_kind kind() const override;
    virtual bool cache() const override;
    virtual bool compact() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

struct OnDiskMachine : public MachineBase
{
    virtual mpt::state_machine_kind kind() const override;
    virtual bool cache() const override;
    virtual bool compact() const override;
    virtual bool auto_expire() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

// In-memory machine that hashes storage at page granularity. Used once the
// chain is at a revision that persists storage as pages instead of slots.
struct MonadInMemoryMachine final : public InMemoryMachine
{
    virtual mpt::state_machine_kind kind() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;

protected:
    virtual mpt::Compute &storage_compute() const override;
    virtual mpt::Compute &storage_root_compute() const override;
};

// On-disk machine that hashes storage at page granularity. Used once the
// chain is at a revision that persists storage as pages instead of slots.
struct MonadOnDiskMachine final : public OnDiskMachine
{
    virtual mpt::state_machine_kind kind() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;

protected:
    virtual mpt::Compute &storage_compute() const override;
    virtual mpt::Compute &storage_root_compute() const override;
};

// Machines for the EIP-8297 partitioned layout (partitioned_layout.hpp): the
// state table is one flat key space of zone keys. Stems (zone || H(addr)) are
// nested roots with an empty value whose node data holds the subtrie hash, so
// a single update erases or replaces an account's header or storage bucket.
// Every leaf is a 32 byte value hashed as is.
struct PartitionedInMemoryMachine final : public InMemoryMachine
{
    virtual mpt::state_machine_kind kind() const override;
    virtual mpt::Compute &get_compute() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

struct PartitionedOnDiskMachine final : public OnDiskMachine
{
    virtual mpt::state_machine_kind kind() const override;
    virtual mpt::Compute &get_compute() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

//////////////////////////////////////////////////////////
// State keys
//////////////////////////////////////////////////////////
// Hash of an address or a storage slot into its trie key. keccak256 as in
// Ethereum, or BLAKE3 when the build hashes nodes with BLAKE3
// (MONAD_MPT_NODE_HASH=blake3), so that a blake3 build is blake3 throughout.
inline monad_hash256 state_key_hash(byte_string_view const v)
{
    if constexpr (mpt::NODE_HASH_BLAKE3) {
        return blake3(v);
    }
    else {
        return keccak256(v);
    }
}

template <size_t N>
inline monad_hash256 state_key_hash(unsigned char const (&a)[N])
{
    return state_key_hash(byte_string_view{a, N});
}

inline monad_hash256 state_key_hash(bytes32_t const &b)
{
    return state_key_hash(byte_string_view{b.bytes, sizeof(b.bytes)});
}

//////////////////////////////////////////////////////////
// Table Nibbles
//////////////////////////////////////////////////////////
inline constexpr unsigned char STATE_NIBBLE = 0;
inline constexpr unsigned char CODE_NIBBLE = 1;
inline constexpr unsigned char RECEIPT_NIBBLE = 2;
inline constexpr unsigned char TRANSACTION_NIBBLE = 3;
inline constexpr unsigned char BLOCKHEADER_NIBBLE = 4;
inline constexpr unsigned char WITHDRAWAL_NIBBLE = 5;
inline constexpr unsigned char OMMER_NIBBLE = 6;
inline constexpr unsigned char TX_HASH_NIBBLE = 7;
inline constexpr unsigned char BLOCK_HASH_NIBBLE = 8;
inline constexpr unsigned char CALL_FRAME_NIBBLE = 9;
inline constexpr unsigned char INVALID_NIBBLE = 255;
inline mpt::Nibbles const state_nibbles = mpt::concat(STATE_NIBBLE);
inline mpt::Nibbles const code_nibbles = mpt::concat(CODE_NIBBLE);
inline mpt::Nibbles const receipt_nibbles = mpt::concat(RECEIPT_NIBBLE);
inline mpt::Nibbles const call_frame_nibbles = mpt::concat(CALL_FRAME_NIBBLE);
inline mpt::Nibbles const transaction_nibbles = mpt::concat(TRANSACTION_NIBBLE);
inline mpt::Nibbles const block_header_nibbles =
    mpt::concat(BLOCKHEADER_NIBBLE);
inline mpt::Nibbles const ommer_nibbles = mpt::concat(OMMER_NIBBLE);
inline mpt::Nibbles const withdrawal_nibbles = mpt::concat(WITHDRAWAL_NIBBLE);
inline mpt::Nibbles const tx_hash_nibbles = mpt::concat(TX_HASH_NIBBLE);
inline mpt::Nibbles const block_hash_nibbles = mpt::concat(BLOCK_HASH_NIBBLE);

//////////////////////////////////////////////////////////
// Proposed and finialized subtries. Active on all tables.
//////////////////////////////////////////////////////////
inline constexpr unsigned char PROPOSAL_NIBBLE = 0;
inline constexpr unsigned char FINALIZED_NIBBLE = 1;
inline mpt::Nibbles const proposal_nibbles = mpt::concat(PROPOSAL_NIBBLE);
inline mpt::Nibbles const finalized_nibbles = mpt::concat(FINALIZED_NIBBLE);

byte_string encode_account_db(Address const &, Account const &);
byte_string encode_storage_db(bytes32_t const &, bytes32_t const &);

// ── Monad Page Storage ──────────────────────────────
//
// DB format: RLP([compact(key), string(encode_storage_page(page))])
//
// encode_storage_page / decode_storage_page live in storage_page.hpp.

byte_string
encode_storage_page_db(bytes32_t const &key, storage_page_t const &page);

Result<std::pair<byte_string_view, byte_string_view>>
decode_account_db_raw(byte_string_view &);
Result<std::pair<Address, Account>> decode_account_db(byte_string_view &);
Result<Account> decode_account_db_ignore_address(byte_string_view &);

Result<std::pair<byte_string_view, byte_string_view>>
decode_storage_db_raw(byte_string_view &);
Result<std::pair<bytes32_t, bytes32_t>> decode_storage_db(byte_string_view &);
Result<byte_string_view> decode_storage_db_ignore_key(byte_string_view &);

// Decode a storage leaf value into a page: the full page for page encoding, a
// single-slot page holding the value at offset 0 for slot encoding. Aborts on
// a malformed leaf.
storage_page_t
decode_storage_leaf_to_page(byte_string_view encoded, bool page_encoded);

// Decode a page-encoded storage leaf (an encode_storage_page_db value) into its
// page key and page; fails on a malformed leaf (including trailing bytes).
Result<DecodedStoragePage> decode_storage_page_leaf(byte_string_view leaf);

struct AccountLeafProcessor
{
    static byte_string process(mpt::Node const &node);
};

struct StorageLeafProcessor
{
    static byte_string process(mpt::Node const &node);
};

Result<std::pair<Receipt, size_t>> decode_receipt_db(byte_string_view &);
Result<std::pair<Transaction, Address>>
decode_transaction_db(byte_string_view &);

void write_to_file(
    nlohmann::json const &, std::filesystem::path const &,
    uint64_t block_number);

mpt::Node::SharedPtr load_from_binary(
    mpt::Db &, std::istream &accounts, std::istream &code,
    uint64_t init_block_number = 0,
    size_t buf_size = 1ul << 32); // TODO: dynamic loading

mpt::Node::SharedPtr
load_header(mpt::Node::SharedPtr, mpt::Db &, BlockHeader const &);

mpt::Nibbles proposal_prefix(bytes32_t const &);

std::vector<bytes32_t> get_proposal_block_ids(mpt::Db &, uint64_t block_number);

template <typename DBType>
    requires std::is_same_v<mpt::Db, DBType> ||
             std::is_same_v<mpt::RODb, DBType>
Result<std::vector<Transaction>> get_transactions(
    DBType &, uint64_t block_number, bytes32_t const &block_id = {});

bool for_each_code(
    mpt::Db &, uint64_t block,
    std::function<void(bytes32_t const &, byte_string_view)>);

MONAD_NAMESPACE_END
