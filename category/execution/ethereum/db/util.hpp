#pragma once

#include <category/core/byte_string.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/state_machine.hpp>

#include <nlohmann/json.hpp>

#include <filesystem>
#include <istream>

MONAD_NAMESPACE_BEGIN

struct BlockHeader;

struct MachineBase : public mpt::StateMachine
{
    static constexpr uint64_t TABLE_PREFIX_LEN = 1;
    static constexpr uint64_t TOP_NIBBLE_PREFIX_LEN = 1;
    static constexpr uint64_t FINALIZED_PREFIX_LEN =
        TOP_NIBBLE_PREFIX_LEN + TABLE_PREFIX_LEN;
    static constexpr uint64_t PROPOSAL_PREFIX_LEN =
        TOP_NIBBLE_PREFIX_LEN +
        sizeof(bytes32_t) * 2 /* use block_id as proposal prefix */ +
        TABLE_PREFIX_LEN;

    enum class TrieType : uint8_t
    {
        Undefined,
        Finalized,
        Proposal
    };

    enum class TableType : uint8_t
    {
        Prefix,
        State,
        Code,
        Receipt,
        Transaction,
        Withdrawal,
        TxHash,
        BlockHash
    };

    uint8_t depth{0};
    TrieType trie_section{TrieType::Undefined};
    TableType table{TableType::Prefix};

    virtual mpt::Compute &get_compute() const override;
    virtual void down(unsigned char const nibble) override;
    virtual void up(size_t const n) override;
    constexpr uint8_t prefix_len() const;

    constexpr uint8_t max_depth(uint8_t const prefix_length) const
    {
        return prefix_length + sizeof(bytes32_t) * 2 + sizeof(bytes32_t) * 2;
    }
};

static_assert(sizeof(MachineBase) == 16);
static_assert(alignof(MachineBase) == 8);

struct InMemoryMachine final : public MachineBase
{
    virtual bool cache() const override;
    virtual bool compact() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

struct OnDiskMachine : public MachineBase
{
    virtual bool cache() const override;
    virtual bool compact() const override;
    virtual bool auto_expire() const override;
    virtual std::unique_ptr<StateMachine> clone() const override;
};

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
inline constexpr unsigned char BFT_BLOCK_NIBBLE = 10;
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
inline mpt::Nibbles const bft_block_nibbles = mpt::concat(BFT_BLOCK_NIBBLE);

//////////////////////////////////////////////////////////
// Proposed and finialized subtries. Active on all tables.
//////////////////////////////////////////////////////////
inline constexpr unsigned char PROPOSAL_NIBBLE = 0;
inline constexpr unsigned char FINALIZED_NIBBLE = 1;
inline mpt::Nibbles const proposal_nibbles = mpt::concat(PROPOSAL_NIBBLE);
inline mpt::Nibbles const finalized_nibbles = mpt::concat(FINALIZED_NIBBLE);

byte_string encode_account_db(Address const &, Account const &);
byte_string encode_storage_db(bytes32_t const &, bytes32_t const &);

Result<std::pair<byte_string_view, byte_string_view>>
decode_account_db_raw(byte_string_view &);
Result<std::pair<Address, Account>> decode_account_db(byte_string_view &);
Result<Account> decode_account_db_ignore_address(byte_string_view &);

Result<std::pair<byte_string_view, byte_string_view>>
decode_storage_db_raw(byte_string_view &);
Result<std::pair<bytes32_t, bytes32_t>> decode_storage_db(byte_string_view &);
Result<byte_string_view> decode_storage_db_ignore_slot(byte_string_view &);

Result<std::pair<Receipt, size_t>> decode_receipt_db(byte_string_view &);
Result<std::pair<Transaction, Address>>
decode_transaction_db(byte_string_view &);

void write_to_file(
    nlohmann::json const &, std::filesystem::path const &,
    uint64_t block_number);

void load_from_binary(
    mpt::Db &, std::istream &accounts, std::istream &code,
    uint64_t init_block_number = 0,
    size_t buf_size = 1ul << 32); // TODO: dynamic loading

void load_header(mpt::Db &, BlockHeader const &);

mpt::Nibbles proposal_prefix(bytes32_t const &);

std::vector<bytes32_t> get_proposal_block_ids(mpt::Db &, uint64_t block_number);

std::optional<BlockHeader>
read_eth_header(mpt::Db const &db, uint64_t block, mpt::NibblesView prefix);

std::optional<byte_string> query_consensus_header(
    mpt::Db const &db, uint64_t block, mpt::NibblesView prefix);

std::optional<MonadConsensusBlockHeader> read_consensus_header(
    mpt::Db const &db, uint64_t block, mpt::NibblesView prefix);

MONAD_NAMESPACE_END
