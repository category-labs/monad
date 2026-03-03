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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/mpt/update.hpp>

#include <deque>
#include <vector>

MONAD_NAMESPACE_BEGIN

struct CallFrame;
struct Transaction;
struct BlockHeader;
struct Receipt;
struct Withdrawal;

class CommitBuilder
{
protected:
    std::deque<mpt::Update> update_alloc_;
    std::deque<byte_string> bytes_alloc_;
    std::deque<hash256> hash_alloc_;
    mpt::UpdateList updates_;
    uint64_t block_number_;

public:
    explicit CommitBuilder(uint64_t block_number);
    virtual ~CommitBuilder() = default;

    virtual CommitBuilder &add_state_deltas(StateDeltas const &);

    CommitBuilder &add_code(Code const &);

    template <typename Range>
    CommitBuilder &add_raw_code(Range const &code_entries)
    {
        mpt::UpdateList code_updates;
        for (auto const &[hash, bytes] : code_entries) {
            code_updates.push_front(update_alloc_.emplace_back(mpt::Update{
                .key = mpt::NibblesView{to_byte_string_view(hash.bytes)},
                .value = byte_string_view{bytes},
                .incarnation = false,
                .next = mpt::UpdateList{},
                .version = static_cast<int64_t>(block_number_)}));
        }
        updates_.push_front(update_alloc_.emplace_back(mpt::Update{
            .key = code_nibbles,
            .value = byte_string_view{},
            .incarnation = false,
            .next = std::move(code_updates),
            .version = static_cast<int64_t>(block_number_)}));
        return *this;
    }

    CommitBuilder &add_receipts(std::vector<Receipt> const &);

    CommitBuilder &add_transactions(
        std::vector<Transaction> const &, std::vector<Address> const &);

    CommitBuilder &add_call_frames(std::vector<std::vector<CallFrame>> const &);

    CommitBuilder &add_ommers(std::vector<BlockHeader> const &);

    CommitBuilder &add_withdrawals(std::vector<Withdrawal> const &);

    CommitBuilder &add_block_header(BlockHeader const &);

    // Consumes updates_ but preserves the backing deque storage. New updates
    // can be added after a build() call (e.g. add_block_header between the
    // two commit stages), but previously built updates are not retained.
    mpt::UpdateList build(mpt::NibblesView);
};

MONAD_NAMESPACE_END
