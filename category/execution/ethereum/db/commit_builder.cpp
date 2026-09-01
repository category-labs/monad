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

#include "commit_builder.hpp"

#include <category/core/assert.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/receipt_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <limits>

MONAD_NAMESPACE_BEGIN

using namespace monad::mpt;

namespace
{
    byte_string
    encode_receipt_db(Receipt const &receipt, size_t const log_index_begin)
    {
        return rlp::encode_list2(
            rlp::encode_string2(rlp::encode_receipt(receipt)),
            rlp::encode_unsigned(log_index_begin));
    }

    byte_string encode_transaction_db(
        byte_string_view const encoded_tx, Address const &sender)
    {
        return rlp::encode_list2(
            rlp::encode_string2(encoded_tx), rlp::encode_address(sender));
    }
}

CommitBuilder::CommitBuilder(
    uint64_t const block_number, monad::Db *const db,
    BlockAccessSets const *const access)
    : block_number_{block_number}
    , db_{db}
    , access_{access}
{
}

void CommitBuilder::bump_account(
    std::optional<Account> const &pre, Account &post)
{
    if (cache_pricing_bump_due(post.last_access_block, block_number_)) {
        post.last_access_block = block_number_;
    }
    if (pre.has_value() && pre->last_access_block != 0) {
        bucket_deltas_[{PricingKind::account, pre->last_access_block}] -= 1;
    }
    if (post.last_access_block != 0) {
        bucket_deltas_[{PricingKind::account, post.last_access_block}] += 1;
    }
}

CommitBuilder &CommitBuilder::add_state_deltas(StateDeltas const &state_deltas)
{
    UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        UpdateList storage_updates;
        std::optional<byte_string_view> value;
        // mutable copy: last_access bumps are applied at commit time only
        std::optional<Account> account = delta.account.second;
        // bump only addresses in the deterministic access set; StateDeltas
        // itself contains reads from aborted speculative attempts
        ankerl::unordered_dense::segmented_set<bytes32_t> const *touched =
            nullptr;
        if (access_ != nullptr) {
            if (auto const it = access_->find(addr); it != access_->end()) {
                touched = &it->second;
            }
            if (account.has_value()) {
                if (touched != nullptr) {
                    bump_account(delta.account.first, *account);
                }
            }
            else if (
                delta.account.first.has_value() &&
                delta.account.first->last_access_block != 0) {
                // deleted account leaves the histogram
                bucket_deltas_[{
                    PricingKind::account,
                    delta.account.first->last_access_block}] -= 1;
            }
        }
        proposal_post_state_.accounts[addr] = account;
        if (account.has_value()) {
            auto const inc = account->incarnation;
            bool const pre_storage_valid =
                delta.account.first.has_value() &&
                delta.account.first->incarnation == inc;
            ankerl::unordered_dense::segmented_set<bytes32_t> written;
            auto const slot_pre_ts = [&](bytes32_t const &key) {
                return pre_storage_valid
                           ? db_->read_storage_page(addr, inc, key).last_access
                           : 0;
            };
            for (auto const &[key, slot_delta] : delta.storage) {
                if (slot_delta.first != slot_delta.second) {
                    bool const deleted = slot_delta.second == bytes32_t{};
                    uint64_t last_access = 0;
                    if (touched != nullptr) {
                        written.insert(key);
                        uint64_t const pre_ts = slot_pre_ts(key);
                        if (pre_ts != 0) {
                            bucket_deltas_[{PricingKind::storage, pre_ts}] -= 1;
                        }
                        if (!deleted) {
                            last_access =
                                cache_pricing_bump_due(pre_ts, block_number_)
                                    ? block_number_
                                    : pre_ts;
                            if (last_access != 0) {
                                bucket_deltas_[{
                                    PricingKind::storage, last_access}] += 1;
                            }
                        }
                    }
                    storage_updates.push_front(
                        update_alloc_.emplace_back(Update{
                            .key = hash_alloc_.emplace_back(
                                keccak256({key.bytes, sizeof(key.bytes)})),
                            .value = deleted
                                         ? std::nullopt
                                         : std::make_optional<byte_string_view>(
                                               bytes_alloc_.emplace_back(
                                                   encode_storage_db(
                                                       key,
                                                       slot_delta.second,
                                                       last_access))),
                            .incarnation = false,
                            .next = UpdateList{},
                            .version = static_cast<int64_t>(block_number_)}));
                    storage_page_t page{slot_delta.second};
                    page.last_access = last_access;
                    proposal_post_state_.storage[StorageKey{addr, inc, key}] =
                        page;
                }
            }

            // read-only touched slots whose last_access is due for a bump
            // become leaf rewrites
            if (touched != nullptr && pre_storage_valid) {
                for (auto const &key : *touched) {
                    if (written.contains(key)) {
                        continue;
                    }
                    storage_page_t page =
                        db_->read_storage_page(addr, inc, key);
                    if (page.is_empty()) {
                        continue;
                    }
                    if (!cache_pricing_bump_due(
                            page.last_access, block_number_)) {
                        continue;
                    }
                    if (page.last_access != 0) {
                        bucket_deltas_[{
                            PricingKind::storage, page.last_access}] -= 1;
                    }
                    page.last_access = block_number_;
                    bucket_deltas_[{PricingKind::storage, block_number_}] += 1;
                    storage_updates.push_front(
                        update_alloc_.emplace_back(Update{
                            .key = hash_alloc_.emplace_back(
                                keccak256({key.bytes, sizeof(key.bytes)})),
                            .value =
                                bytes_alloc_.emplace_back(encode_storage_db(
                                    key, page[0], page.last_access)),
                            .incarnation = false,
                            .next = UpdateList{},
                            .version = static_cast<int64_t>(block_number_)}));
                    proposal_post_state_.storage[StorageKey{addr, inc, key}] =
                        page;
                }
            }
            value = bytes_alloc_.emplace_back(
                encode_account_db(addr, account.value()));
        }

        if (!storage_updates.empty() || delta.account.first != account) {
            bool const incarnation =
                account.has_value() && delta.account.first.has_value() &&
                delta.account.first->incarnation != account->incarnation;
            account_updates.push_front(update_alloc_.emplace_back(Update{
                .key = hash_alloc_.emplace_back(
                    keccak256({addr.bytes, sizeof(addr.bytes)})),
                .value = value,
                .incarnation = incarnation,
                .next = std::move(storage_updates),
                .version = static_cast<int64_t>(block_number_)}));
        }
    }

    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates),
        .version = static_cast<int64_t>(block_number_)}));

    if (access_ != nullptr) {
        add_pricing_updates();
    }

    return *this;
}

void CommitBuilder::add_pricing_updates()
{
    auto const read_bucket = [this](PricingKind const kind, uint64_t const b) {
        return kind == PricingKind::account
                   ? db_->read_account_pricing_bucket(b)
                   : db_->read_storage_pricing_bucket(b);
    };
    // prune the bucket falling out of the window: increments only happen at
    // the bucket's own block, so bucket b is dead after block b + W
    if (block_number_ > CACHE_PRICING_WINDOW) {
        for (auto const kind : {PricingKind::account, PricingKind::storage}) {
            uint64_t const b = block_number_ - CACHE_PRICING_WINDOW - 1;
            if (read_bucket(kind, b).has_value()) {
                bucket_deltas_.try_emplace({kind, b}, 0);
            }
        }
    }

    uint64_t const window_floor = block_number_ > CACHE_PRICING_WINDOW
                                      ? block_number_ - CACHE_PRICING_WINDOW
                                      : 0;
    UpdateList bucket_updates;
    for (auto const &[bucket, delta] : bucket_deltas_) {
        auto const [kind, block] = bucket;
        bool const pruned = block < window_floor;
        if (delta == 0 && !pruned) {
            continue;
        }
        int64_t const current =
            static_cast<int64_t>(read_bucket(kind, block).value_or(0));
        if (pruned && current == 0) {
            continue;
        }
        int64_t const weight = pruned ? 0 : current + delta;
        MONAD_ASSERT(weight >= 0);
        bucket_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{bytes_alloc_.emplace_back(
                cache_pricing_bucket_key(kind, block))},
            .value = weight > 0
                         ? std::make_optional<byte_string_view>(
                               bytes_alloc_.emplace_back(rlp::encode_unsigned(
                                   static_cast<uint64_t>(weight))))
                         : std::nullopt,
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }
    if (bucket_updates.empty()) {
        return;
    }
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = cache_pricing_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(bucket_updates),
        .version = static_cast<int64_t>(block_number_)}));
}

CommitBuilder &CommitBuilder::add_code(Code const &code)
{
    UpdateList code_updates;
    for (auto const &[hash, icode] : code) {
        MONAD_ASSERT(icode);
        code_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{to_byte_string_view(hash.bytes)},
            .value = {{icode->code(), icode->size()}},
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = code_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(code_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &CommitBuilder::add_receipts(std::vector<Receipt> const &receipts)
{
    UpdateList receipt_updates;
    MONAD_ASSERT(receipts.size() <= std::numeric_limits<uint32_t>::max());

    size_t log_index_begin = 0;
    for (uint32_t i = 0; i < static_cast<uint32_t>(receipts.size()); ++i) {
        auto const &rlp_index =
            bytes_alloc_.emplace_back(rlp::encode_unsigned(i));
        auto const &receipt = receipts[i];
        auto const &encoded_receipt = bytes_alloc_.emplace_back(
            encode_receipt_db(receipt, log_index_begin));
        log_index_begin += receipt.logs.size();

        receipt_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{rlp_index},
            .value = encoded_receipt,
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = receipt_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(receipt_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &CommitBuilder::add_transactions(
    std::vector<Transaction> const &transactions,
    std::vector<Address> const &senders)
{
    UpdateList txn_updates;
    UpdateList txn_hash_updates;

    MONAD_ASSERT(transactions.size() <= std::numeric_limits<uint32_t>::max());
    MONAD_ASSERT(transactions.size() == senders.size());

    auto const encoded_block_number =
        bytes_alloc_.emplace_back(rlp::encode_unsigned(block_number_));

    for (uint32_t i = 0; i < static_cast<uint32_t>(transactions.size()); ++i) {
        auto const &rlp_index =
            bytes_alloc_.emplace_back(rlp::encode_unsigned(i));

        auto const encoded_tx = rlp::encode_transaction(transactions[i]);
        txn_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{rlp_index},
            .value = bytes_alloc_.emplace_back(
                encode_transaction_db(encoded_tx, senders[i])),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));

        txn_hash_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{hash_alloc_.emplace_back(keccak256(encoded_tx))},
            .value = bytes_alloc_.emplace_back(
                rlp::encode_list2(encoded_block_number, rlp_index)),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }

    // txns subtrie
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = transaction_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(txn_updates),
        .version = static_cast<int64_t>(block_number_)}));

    // txns hash subtrie
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = tx_hash_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(txn_hash_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &CommitBuilder::add_call_frames(
    std::vector<std::vector<CallFrame>> const &call_frames)
{
    UpdateList call_frame_updates;

    MONAD_ASSERT(call_frames.size() <= std::numeric_limits<uint32_t>::max());

    for (uint32_t i = 0; i < static_cast<uint32_t>(call_frames.size()); ++i) {
        byte_string_view frame_view =
            bytes_alloc_.emplace_back(rlp::encode_call_frames(call_frames[i]));
        uint8_t chunk_index = 0;
        auto const call_frame_prefix =
            serialize_as_big_endian<sizeof(uint32_t)>(i);

        while (!frame_view.empty()) {
            MONAD_ASSERT(chunk_index <= std::numeric_limits<uint8_t>::max());
            byte_string_view chunk =
                frame_view.substr(0, MAX_VALUE_LEN_OF_LEAF);
            frame_view.remove_prefix(chunk.size());
            byte_string const chunk_key =
                byte_string{&chunk_index, sizeof(uint8_t)};
            call_frame_updates.push_front(update_alloc_.emplace_back(Update{
                .key = bytes_alloc_.emplace_back(call_frame_prefix + chunk_key),
                .value = chunk,
                .incarnation = false,
                .next = UpdateList{},
                .version = static_cast<int64_t>(block_number_)}));
            ++chunk_index;
        }
    }
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = call_frame_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(call_frame_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &CommitBuilder::add_ommers(std::vector<BlockHeader> const &ommers)
{
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = ommer_nibbles,
        .value = bytes_alloc_.emplace_back(rlp::encode_ommers(ommers)),
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &
CommitBuilder::add_withdrawals(std::vector<Withdrawal> const &withdrawals)
{
    UpdateList withdrawal_updates;

    for (size_t i = 0; i < withdrawals.size(); ++i) {
        auto const &rlp_index =
            bytes_alloc_.emplace_back(rlp::encode_unsigned(i));

        withdrawal_updates.push_front(update_alloc_.emplace_back(Update{
            .key = NibblesView{rlp_index},
            .value = bytes_alloc_.emplace_back(
                rlp::encode_withdrawal(withdrawals[i])),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(block_number_)}));
    }
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = withdrawal_nibbles,
        .value = byte_string_view{},
        .incarnation = true,
        .next = std::move(withdrawal_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

CommitBuilder &CommitBuilder::add_block_header(BlockHeader const &header)
{
    auto const eth_header_rlp = rlp::encode_block_header(header);

    UpdateList block_hash_nested_updates;
    block_hash_nested_updates.push_front(update_alloc_.emplace_back(Update{
        .key = hash_alloc_.emplace_back(keccak256(eth_header_rlp)),
        .value = bytes_alloc_.emplace_back(rlp::encode_unsigned(header.number)),
        .incarnation = false,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)}));

    // block header subtrie
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = block_header_nibbles,
        .value = bytes_alloc_.emplace_back(eth_header_rlp),
        .incarnation = true,
        .next = UpdateList{},
        .version = static_cast<int64_t>(block_number_)}));

    // block hash subtrie
    updates_.push_front(update_alloc_.emplace_back(Update{
        .key = block_hash_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(block_hash_nested_updates),
        .version = static_cast<int64_t>(block_number_)}));

    return *this;
}

UpdateList CommitBuilder::build(NibblesView const prefix)
{
    UpdateList root_update;
    root_update.push_front(update_alloc_.emplace_back(Update{
        .key = prefix,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(updates_),
        .version = static_cast<int64_t>(block_number_)}));
    return root_update;
}

MONAD_NAMESPACE_END
