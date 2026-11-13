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
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/util.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <vector>

MONAD_DOMAIN_NAMESPACE_BEGIN

TrieDbL1Source::TrieDbL1Source(mpt::Db &db)
    : db_{db}
{
    // By the time any domain is introduced, the L1 network's db is
    // page-encoded.
    MONAD_ASSERT(db_.state_machine_type() == mpt::state_machine_kind::monad);
}

uint64_t TrieDbL1Source::latest_finalized() const
{
    return db_.get_latest_finalized_version();
}

Result<BlockHeader>
TrieDbL1Source::read_finalized_header(uint64_t const number) const
{
    auto const latest = latest_finalized();
    if (latest == mpt::INVALID_BLOCK_NUM || number > latest) {
        return mpt::DbError::version_no_longer_exist;
    }

    BOOST_OUTCOME_TRY(
        auto const cursor,
        db_.find(
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            number));
    byte_string_view encoded{cursor.node->value()};
    BOOST_OUTCOME_TRY(auto const header, rlp::decode_block_header(encoded));
    MONAD_ASSERT(header.number == number);
    return header;
}

Result<std::vector<Receipt>>
TrieDbL1Source::read_finalized_receipts(uint64_t const number) const
{
    auto const latest = latest_finalized();
    if (latest == mpt::INVALID_BLOCK_NUM || number > latest) {
        return mpt::DbError::version_no_longer_exist;
    }

    return get_receipts(db_, number);
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
    // The db is page-encoded: a slot is in the leaf of its page.
    bytes32_t const page_key = compute_page_key(slot);
    auto const leaf = db_.find(
        mpt::concat(
            FINALIZED_NIBBLE,
            STATE_NIBBLE,
            mpt::NibblesView{keccak256({address.bytes, sizeof(address.bytes)})},
            mpt::NibblesView{
                keccak256({page_key.bytes, sizeof(page_key.bytes)})}),
        number);
    if (leaf.has_error()) {
        if (leaf.error() == mpt::DbError::version_no_longer_exist) {
            return mpt::DbError::version_no_longer_exist;
        }
        return bytes32_t{};
    }
    auto const page =
        decode_storage_leaf_to_page(leaf.value().node->value(), true);
    return page[compute_slot_offset(slot)];
}

MONAD_DOMAIN_NAMESPACE_END
