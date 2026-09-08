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

#include <category/vm/runtime/access.hpp>

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
#include <category/execution/ethereum/db/storage_key.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/rlp/call_frame_rlp.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <algorithm>
#include <cstring>
#include <limits>
#include <vector>

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
    uint64_t const block_number, StampContext const *const stamps)
    : block_number_{block_number}
    , stamps_{stamps}
{
}

// One stamp record per key: the entry is stamped to this block (weight != 0)
// or its stamp is dropped (weight == 0). prev values come from the stamps
// memoized by the block's reads; the windows decrement them exactly.
void CommitBuilder::add_stamp_records(StateDeltas const &state_deltas)
{
    uint64_t const n = block_number_;
    auto const &bounds = stamps_->boundaries;
    ankerl::unordered_dense::segmented_set<Address> seen_accounts;
    ankerl::unordered_dense::
        segmented_set<StorageKey, BytesHashCompare<StorageKey>>
            seen_storage;
    auto &account_records = proposal_post_state_.account_stamps;
    auto &storage_records = proposal_post_state_.storage_stamps;
    auto const capped = [&] {
        return account_records.size() + storage_records.size() >=
               K_STAMP_CEILING;
    };
    auto const slot_weight = [](bytes32_t const &value) {
        return value == bytes32_t{}
                   ? uint32_t{0}
                   : static_cast<uint32_t>(storage_page_t{value}.byte_size());
    };

    // write-stamps: value-changing writes stamp unconditionally; deletions
    // drop the stamp. Keys sorted for a deterministic record stream.
    std::vector<Address> write_addrs;
    for (auto const &[addr, delta] : state_deltas) {
        write_addrs.push_back(addr);
    }
    std::sort(
        write_addrs.begin(),
        write_addrs.end(),
        [](auto const &a, auto const &b) {
            return std::memcmp(a.bytes, b.bytes, sizeof(a.bytes)) < 0;
        });
    for (auto const &addr : write_addrs) {
        if (capped()) {
            break;
        }
        StateDeltas::const_accessor it{};
        MONAD_ASSERT(state_deltas.find(it, addr));
        auto const &delta = it->second;
        auto const &pre = delta.account.first;
        auto const &post = delta.account.second;
        if (pre != post) {
            account_records.push_back(AccountStampRecord{
                .address = addr,
                .prev_stamp = delta.account_stamp.value_or(0),
                .prev_weight = pre.has_value() ? uint8_t{1} : uint8_t{0},
                .weight = post.has_value() ? uint8_t{1} : uint8_t{0}});
            seen_accounts.insert(addr);
        }
        if (!post.has_value()) {
            // TODO: storage stamps under a deleted or reincarnated account
            // are not enumerated here; their window weight leaks until the
            // physical entries expire (overcharge direction, and extinct
            // organically since Cancun)
            continue;
        }
        bool const reincarnated =
            pre.has_value() && pre->incarnation != post->incarnation;
        std::vector<bytes32_t> keys;
        for (auto const &[key, slot] : delta.storage) {
            if (slot.first != slot.second) {
                keys.push_back(key);
            }
        }
        std::sort(keys.begin(), keys.end(), [](auto const &a, auto const &b) {
            return std::memcmp(a.bytes, b.bytes, sizeof(a.bytes)) < 0;
        });
        for (auto const &key : keys) {
            if (capped()) {
                break;
            }
            StorageDeltas::const_accessor sit{};
            MONAD_ASSERT(delta.storage.find(sit, key));
            auto const &[pre_value, post_value] = sit->second;
            uint64_t prev_stamp = 0;
            uint32_t prev_weight = 0;
            if (!reincarnated) {
                auto const mit = delta.storage_stamps.find(key);
                prev_stamp =
                    mit != delta.storage_stamps.end() ? mit->second : 0;
                prev_weight = slot_weight(pre_value);
            }
            StorageKey const skey{addr, post->incarnation, key};
            storage_records.push_back(StorageStampRecord{
                .key = skey,
                .prev_stamp = prev_stamp,
                .prev_weight = prev_weight,
                .weight = slot_weight(post_value)});
            seen_storage.insert(skey);
        }
    }

    // read-stamps: cold accesses of live pre-state entries stamp; warm-set
    // (cached tier) reads re-stamp only when stale per the lazy refresh rule
    for (auto const &tx : *stamps_->candidates) {
        if (capped()) {
            break;
        }
        std::vector<Address> addrs = tx.accounts;
        std::sort(addrs.begin(), addrs.end(), [](auto const &a, auto const &b) {
            return std::memcmp(a.bytes, b.bytes, sizeof(a.bytes)) < 0;
        });
        for (auto const &addr : addrs) {
            if (capped()) {
                break;
            }
            if (seen_accounts.contains(addr)) {
                continue;
            }
            StateDeltas::const_accessor it{};
            if (!state_deltas.find(it, addr) ||
                !it->second.account.first.has_value()) {
                continue;
            }
            uint64_t const prev = it->second.account_stamp.value_or(0);
            bool const cold = prev == 0 || prev < bounds.account;
            if (!cold && !cache_stamp_refresh_due(prev, n, bounds.account)) {
                continue;
            }
            account_records.push_back(AccountStampRecord{
                .address = addr,
                .prev_stamp = prev,
                .prev_weight = 1,
                .weight = 1});
            seen_accounts.insert(addr);
        }
        std::vector<std::pair<Address, bytes32_t>> slots = tx.storage;
        std::sort(slots.begin(), slots.end(), [](auto const &a, auto const &b) {
            int const c = std::memcmp(
                a.first.bytes, b.first.bytes, sizeof(a.first.bytes));
            if (c != 0) {
                return c < 0;
            }
            return std::memcmp(
                       a.second.bytes, b.second.bytes, sizeof(a.second.bytes)) <
                   0;
        });
        for (auto const &[addr, key] : slots) {
            if (capped()) {
                break;
            }
            StateDeltas::const_accessor it{};
            if (!state_deltas.find(it, addr)) {
                continue;
            }
            auto const &delta = it->second;
            auto const &pre = delta.account.first;
            auto const &post = delta.account.second;
            // stamp identity is (address, incarnation, key): only reads at
            // the pre-state incarnation qualify
            if (!pre.has_value() || !post.has_value() ||
                pre->incarnation != post->incarnation) {
                continue;
            }
            StorageKey const skey{addr, pre->incarnation, key};
            if (seen_storage.contains(skey)) {
                continue;
            }
            bytes32_t pre_value{};
            {
                StorageDeltas::const_accessor sit{};
                if (!delta.storage.find(sit, key)) {
                    continue;
                }
                pre_value = sit->second.first;
            }
            if (pre_value == bytes32_t{}) {
                // reads of nonexistent slots never stamp
                continue;
            }
            auto const mit = delta.storage_stamps.find(key);
            uint64_t const prev =
                mit != delta.storage_stamps.end() ? mit->second : 0;
            bool const cold = prev == 0 || prev < bounds.storage;
            if (!cold && !cache_stamp_refresh_due(prev, n, bounds.storage)) {
                continue;
            }
            uint32_t const w = slot_weight(pre_value);
            storage_records.push_back(StorageStampRecord{
                .key = skey,
                .prev_stamp = prev,
                .prev_weight = w,
                .weight = w});
            seen_storage.insert(skey);
        }
    }

    vm::runtime::g_cache_shadow_stats.account_stamp_records.fetch_add(
        account_records.size(), std::memory_order_relaxed);
    vm::runtime::g_cache_shadow_stats.storage_stamp_records.fetch_add(
        storage_records.size(), std::memory_order_relaxed);
}

CommitBuilder &CommitBuilder::add_state_deltas(StateDeltas const &state_deltas)
{
    UpdateList account_updates;
    for (auto const &[addr, delta] : state_deltas) {
        UpdateList storage_updates;
        std::optional<byte_string_view> value;
        auto const &account = delta.account.second;
        proposal_post_state_.accounts[addr] = account;
        if (account.has_value()) {
            auto const inc = account->incarnation;
            for (auto const &[key, delta] : delta.storage) {
                if (delta.first != delta.second) {
                    storage_updates.push_front(
                        update_alloc_.emplace_back(Update{
                            .key = hash_alloc_.emplace_back(
                                keccak256({key.bytes, sizeof(key.bytes)})),
                            .value = delta.second == bytes32_t{}
                                         ? std::nullopt
                                         : std::make_optional<byte_string_view>(
                                               bytes_alloc_.emplace_back(
                                                   encode_storage_db(
                                                       key, delta.second))),
                            .incarnation = false,
                            .next = UpdateList{},
                            .version = static_cast<int64_t>(block_number_)}));
                    proposal_post_state_.storage[StorageKey{addr, inc, key}] =
                        storage_page_t{delta.second};
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

    if (stamps_ != nullptr) {
        add_stamp_records(state_deltas);
    }

    return *this;
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
