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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node_cursor.hpp>
#include <category/mpt/util.hpp>

#include <boost/outcome/try.hpp>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_DOMAIN_NAMESPACE_BEGIN

TrieDbL1Source::TrieDbL1Source(mpt::Db const &db)
    : db_{db}
{
}

std::optional<uint64_t> TrieDbL1Source::latest_finalized() const
{
    auto const version = db_.get_latest_finalized_version();
    if (version == mpt::INVALID_BLOCK_NUM) {
        return std::nullopt;
    }
    return version;
}

Result<L1Block> TrieDbL1Source::read_finalized(uint64_t const number) const
{
    // Every find checks that `number` is still in the db's history. They share
    // one root, so nodes loaded by one lookup are reused by the next.
    mpt::NodeCursor const root{db_.load_root_for_version(number)};
    BOOST_OUTCOME_TRY(
        auto const header_cursor,
        db_.find(
            root,
            mpt::concat(
                FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
            number));
    byte_string_view encoded_header{header_cursor.node->value()};

    L1Block block;
    block.hash = to_bytes(keccak256(encoded_header));
    BOOST_OUTCOME_TRY(block.header, rlp::decode_block_header(encoded_header));
    MONAD_ASSERT(block.header.number == number);

    // The receipt table holds one receipt per transaction, keyed by its rlp
    // encoded index.
    for (uint64_t i = 0;; ++i) {
        auto receipt_cursor = db_.find(
            root,
            mpt::concat(
                FINALIZED_NIBBLE,
                mpt::NibblesView{receipt_nibbles},
                mpt::NibblesView{rlp::encode_unsigned(i)}),
            number);
        if (receipt_cursor.has_error()) {
            if (receipt_cursor.assume_error() == mpt::DbError::key_not_found) {
                break;
            }
            return std::move(receipt_cursor).assume_error();
        }
        byte_string_view encoded{receipt_cursor.value().node->value()};
        BOOST_OUTCOME_TRY(auto receipt, decode_receipt_db(encoded));
        block.receipts.push_back(std::move(receipt.first));
    }
    return block;
}

MONAD_DOMAIN_NAMESPACE_END
