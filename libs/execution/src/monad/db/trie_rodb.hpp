#pragma once

#include <monad/config.hpp>
#include <monad/core/keccak.hpp>
#include <monad/db/db.hpp>
#include <monad/db/util.hpp>
#include <monad/mpt/db.hpp>

#include <memory>
#include <optional>

MONAD_NAMESPACE_BEGIN

class TrieRODb final : public ::monad::Db
{
    ::monad::mpt::RODb &db_;
    uint64_t block_number_;
    ::monad::mpt::OwningNodeCursor prefix_cursor_;

public:
    TrieRODb(mpt::RODb &db)
        : db_(db)
        , block_number_(mpt::INVALID_BLOCK_ID)
        , prefix_cursor_()
    {
    }

    ~TrieRODb() = default;

    virtual void set_block_and_round(
        uint64_t const block_number,
        std::optional<uint64_t> const round_number = std::nullopt) override
    {
        auto prefix = round_number.has_value()
                          ? proposal_prefix(round_number.value())
                          : finalized_nibbles;
        auto res = db_.find(prefix, block_number);
        // TODO: error handling instead of assert
        MONAD_ASSERT_PRINTF(
            res.has_value(),
            "block %lu, round %lu",
            block_number,
            round_number.value_or(mpt::INVALID_ROUND_NUM));
        prefix_cursor_ = res.value();
        block_number_ = block_number;
    }

    virtual std::optional<Account> read_account(Address const &addr) override
    {
        auto acc_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})}),
            block_number_);
        if (!acc_leaf_res.has_value()) {
            return std::nullopt;
        }
        auto encoded_account = acc_leaf_res.value().node->value();
        auto const acct = decode_account_db_ignore_address(encoded_account);
        MONAD_DEBUG_ASSERT(!acct.has_error());
        return acct.value();
    }

    virtual bytes32_t read_storage(
        Address const &addr, Incarnation, bytes32_t const &key) override
    {
        auto storage_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                STATE_NIBBLE,
                mpt::NibblesView{keccak256({addr.bytes, sizeof(addr.bytes)})},
                mpt::NibblesView{keccak256({key.bytes, sizeof(key.bytes)})}),
            block_number_);
        if (!storage_leaf_res.has_value()) {
            return {};
        }
        auto encoded_storage = storage_leaf_res.value().node->value();
        auto const storage = decode_storage_db_ignore_slot(encoded_storage);
        MONAD_ASSERT(!storage.has_error());
        return to_bytes(storage.value());
    }

    virtual std::shared_ptr<CodeAnalysis>
    read_code(bytes32_t const &code_hash) override
    {
        // TODO read code analysis object
        auto code_leaf_res = db_.find(
            prefix_cursor_,
            mpt::concat(
                CODE_NIBBLE,
                mpt::NibblesView{to_byte_string_view(code_hash.bytes)}),
            block_number_);
        if (!code_leaf_res.has_value()) {
            return std::make_shared<CodeAnalysis>(analyze({}));
        }
        return std::make_shared<CodeAnalysis>(
            analyze(code_leaf_res.value().node->value()));
    }

    virtual void commit(
        StateDeltas const &, Code const &, MonadConsensusBlockHeader const &,
        std::vector<Receipt> const & = {},
        std::vector<std::vector<CallFrame>> const & = {},
        std::vector<Address> const & = {},
        std::vector<Transaction> const & = {},
        std::vector<BlockHeader> const & = {},
        std::optional<std::vector<Withdrawal>> const & = std::nullopt) override
    {
        MONAD_ABORT();
    }

    virtual void finalize(uint64_t, uint64_t) override
    {
        MONAD_ABORT();
    }

    virtual void update_verified_block(uint64_t) override
    {
        MONAD_ABORT();
    }

    virtual void update_voted_metadata(uint64_t, uint64_t) override
    {
        MONAD_ABORT();
    }

    virtual BlockHeader read_eth_header() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t state_root() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t receipts_root() override
    {
        MONAD_ABORT();
    }

    virtual bytes32_t transactions_root() override
    {
        MONAD_ABORT();
    }

    virtual std::optional<bytes32_t> withdrawals_root() override
    {
        MONAD_ABORT();
    }
};

MONAD_NAMESPACE_END
