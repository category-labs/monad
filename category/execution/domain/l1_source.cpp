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

#include <category/execution/domain/l1_source.hpp>

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/traverse_util.hpp>
#include <category/mpt/util.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <utility>

MONAD_DOMAIN_NAMESPACE_BEGIN

TrieDbL1Source::TrieDbL1Source(mpt::Db &db)
    : db_{db}
{
}

uint64_t TrieDbL1Source::latest_finalized() const
{
    return db_.get_latest_finalized_version();
}

Result<L1Block> TrieDbL1Source::read_finalized(uint64_t const number) const
{
    auto const latest = latest_finalized();
    if (latest == mpt::INVALID_BLOCK_NUM || number > latest) {
        return mpt::DbError::version_no_longer_exist;
    }

    BOOST_OUTCOME_TRY(
        auto const header_cursor,
        db_.find(
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            number));
    byte_string_view encoded_header{header_cursor.node->value()};

    L1Block block;
    block.hash = to_bytes(keccak256(encoded_header));
    BOOST_OUTCOME_TRY(block.header, rlp::decode_block_header(encoded_header));
    MONAD_ASSERT(block.header.number == number);

    // Traverse the receipt table for this block.
    BOOST_OUTCOME_TRY(
        auto const receipts_cursor,
        db_.find(
            mpt::concat(FINALIZED_NIBBLE, mpt::NibblesView{receipt_nibbles}),
            number));
    mpt::GetAllMachine machine{
        [&receipts = block.receipts](
            mpt::NibblesView const path, byte_string_view value) {
            MONAD_ASSERT(path.nibble_size() == path.data_size() * 2);
            byte_string_view raw{path.data(), path.data_size()};
            auto const index = rlp::decode_unsigned<uint32_t>(raw);
            MONAD_ASSERT(index.has_value());
            auto receipt = decode_receipt_db(value);
            MONAD_ASSERT(receipt.has_value());
            if (index.value() >= receipts.size()) {
                receipts.resize(index.value() + 1);
            }
            receipts[index.value()] = std::move(receipt.value().first);
        }};
    if (!db_.traverse(receipts_cursor, machine, number)) {
        MONAD_ASSERT(db_.find({}, number).has_error());
        return mpt::DbError::version_no_longer_exist;
    }
    return block;
}

uint64_t TrieDbL1Source::earliest() const
{
    return db_.get_earliest_version();
}

Result<bytes32_t> TrieDbL1Source::read_storage(
    uint64_t const number, Address const &address, bytes32_t const &slot) const
{
    auto const latest = latest_finalized();
    if (latest == mpt::INVALID_BLOCK_NUM || number > latest) {
        return mpt::DbError::version_no_longer_exist;
    }
    // A page-encoded db keeps a slot in the leaf of its page.
    bool const page_encoded =
        db_.state_machine_type() == mpt::state_machine_kind::monad;
    bytes32_t const lookup_key = page_encoded ? compute_page_key(slot) : slot;
    auto const leaf = db_.find(
        mpt::concat(
            FINALIZED_NIBBLE,
            STATE_NIBBLE,
            mpt::NibblesView{keccak256({address.bytes, sizeof(address.bytes)})},
            mpt::NibblesView{
                keccak256({lookup_key.bytes, sizeof(lookup_key.bytes)})}),
        number);
    if (leaf.has_error()) {
        if (leaf.error() == mpt::DbError::version_no_longer_exist) {
            return mpt::DbError::version_no_longer_exist;
        }
        return bytes32_t{};
    }
    auto const page =
        decode_storage_leaf_to_page(leaf.value().node->value(), page_encoded);
    return page[page_encoded ? compute_slot_offset(slot) : 0];
}

MONAD_DOMAIN_NAMESPACE_END
