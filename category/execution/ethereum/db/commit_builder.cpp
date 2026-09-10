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
#include <category/execution/monad/db/stamp_log.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/update.hpp>
#include <category/mpt/util.hpp>

#include <ankerl/unordered_dense.h>

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

void CommitBuilder::push_state_update(UpdateList &&account_updates)
{
    state_update_ = &update_alloc_.emplace_back(Update{
        .key = state_nibbles,
        .value = byte_string_view{},
        .incarnation = false,
        .next = std::move(account_updates),
        .version = static_cast<int64_t>(block_number_)});
    updates_.push_front(*state_update_);
}

namespace
{
    // Candidate classes (lower stamps first): entry (a cold access to a live
    // item), write renewal (a value-changing write to a cached item), read
    // refresh (a cached read of a stale item).
    constexpr uint8_t STAMP_CLASS_ENTRY = 1;
    constexpr uint8_t STAMP_CLASS_RENEWAL = 2;
    constexpr uint8_t STAMP_CLASS_REFRESH = 3;

    struct AccountCandidate
    {
        uint8_t cls;
        Address address;
    };

    struct PageCandidate
    {
        uint8_t cls;
        uint32_t weight;
        StorageKey key;
    };

    template <class Map, class Key>
    void lower_class(Map &map, Key const &key, uint8_t const cls)
    {
        auto const [it, inserted] = map.try_emplace(key, cls);
        if (!inserted && cls < it->second) {
            it->second = cls;
        }
    }

    uint8_t access_class(uint64_t const prev_stamp, uint64_t const block)
    {
        if (!cache_stamp_cached(prev_stamp, block)) {
            return STAMP_CLASS_ENTRY;
        }
        return cache_stamp_stale(prev_stamp, block) ? STAMP_CLASS_REFRESH : 0;
    }
}

// Selection is a pure function of the block's execution and the parent
// state, so every node derives the same record: candidates sorted by
// (class, weight, key), accounts cut at MAX_ACCOUNT_STAMPS_PER_BLOCK, pages
// at the longest prefix whose occupied slots fit
// MAX_STORAGE_SLOT_STAMPS_PER_BLOCK. Unselected candidates keep their old
// stamp; items that die in the block are not candidates.
void CommitBuilder::add_stamp_records(StateDeltas const &state_deltas)
{
    uint64_t const n = block_number_;
    auto &stats = stamp_stats_;

    ankerl::unordered_dense::segmented_map<Address, uint8_t> account_classes;
    ankerl::unordered_dense::
        segmented_map<StorageKey, uint8_t, BytesHashCompare<StorageKey>>
            page_classes;

    // written items and class 2 (write renewal) from the deltas
    for (auto const &[addr, delta] : state_deltas) {
        if (addr == STAMP_LOG_ADDRESS) {
            continue;
        }
        auto const &pre = delta.account.first;
        auto const &post = delta.account.second;
        if (pre != post) {
            ++stats.accounts_written;
            if (pre.has_value() && post.has_value() &&
                cache_stamp_cached(delta.account_stamp.value_or(0), n)) {
                lower_class(account_classes, addr, STAMP_CLASS_RENEWAL);
            }
        }
        if (!post.has_value()) {
            continue;
        }
        for (auto const &[key, slot] : delta.storage) {
            if (slot.first == slot.second) {
                continue;
            }
            // a reincarnated account never read its old pages, so their
            // memoized stamps are 0 and cannot renew
            auto const mit = delta.storage_stamps.find(key);
            uint64_t const prev =
                mit != delta.storage_stamps.end() ? mit->second : 0;
            if (cache_stamp_cached(prev, n)) {
                lower_class(
                    page_classes,
                    StorageKey{addr, post->incarnation, stamp_lookup_key(key)},
                    STAMP_CLASS_RENEWAL);
            }
        }
    }
    stats.pages_written = proposal_post_state_.storage.size();
    for (auto const &[key, page] : proposal_post_state_.storage) {
        stats.slots_written += page.size();
    }

    // classes 1 and 3 from the journaled read candidates: first accesses of
    // live pre-state items whose tier was not warm
    for (auto const &tx : *stamps_->candidates) {
        for (auto const &addr : tx.accounts) {
            if (addr == STAMP_LOG_ADDRESS) {
                continue;
            }
            StateDeltas::const_accessor it{};
            if (!state_deltas.find(it, addr) ||
                !it->second.account.first.has_value()) {
                continue;
            }
            uint8_t const cls =
                access_class(it->second.account_stamp.value_or(0), n);
            if (cls != 0) {
                lower_class(account_classes, addr, cls);
            }
        }
        for (auto const &[addr, key] : tx.storage) {
            if (addr == STAMP_LOG_ADDRESS) {
                continue;
            }
            StateDeltas::const_accessor it{};
            if (!state_deltas.find(it, addr)) {
                continue;
            }
            auto const &delta = it->second;
            auto const &pre = delta.account.first;
            auto const &post = delta.account.second;
            // stamp identity is (address, incarnation, page): only reads at
            // the pre-state incarnation qualify
            if (!pre.has_value() || !post.has_value() ||
                pre->incarnation != post->incarnation) {
                continue;
            }
            {
                StorageDeltas::const_accessor sit{};
                if (!delta.storage.find(sit, key) ||
                    sit->second.first == bytes32_t{}) {
                    continue; // reads of nonexistent slots never stamp
                }
            }
            auto const mit = delta.storage_stamps.find(key);
            uint8_t const cls = access_class(
                mit != delta.storage_stamps.end() ? mit->second : 0, n);
            if (cls != 0) {
                lower_class(
                    page_classes,
                    StorageKey{addr, pre->incarnation, stamp_lookup_key(key)},
                    cls);
            }
        }
    }

    // materialize, dropping items that die in this block
    std::vector<AccountCandidate> accounts;
    accounts.reserve(account_classes.size());
    for (auto const &[addr, cls] : account_classes) {
        auto const pit = proposal_post_state_.accounts.find(addr);
        if (pit != proposal_post_state_.accounts.end() &&
            !pit->second.has_value()) {
            continue;
        }
        ++stats.account_candidates[cls - 1];
        accounts.push_back({cls, addr});
    }
    std::vector<PageCandidate> pages;
    pages.reserve(page_classes.size());
    for (auto const &[key, cls] : page_classes) {
        uint32_t weight = 0;
        auto const pit = proposal_post_state_.storage.find(key);
        if (pit != proposal_post_state_.storage.end()) {
            if (pit->second.is_empty()) {
                continue;
            }
            weight = static_cast<uint32_t>(pit->second.size());
        }
        else {
            Address addr;
            Incarnation inc{0, 0};
            bytes32_t lookup;
            std::memcpy(addr.bytes, key.bytes, sizeof(addr.bytes));
            std::memcpy(&inc, key.bytes + sizeof(addr.bytes), sizeof(inc));
            std::memcpy(
                lookup.bytes,
                key.bytes + sizeof(addr.bytes) + sizeof(inc),
                sizeof(lookup.bytes));
            weight = stamp_read_weight(addr, inc, lookup);
            if (weight == 0) {
                continue;
            }
        }
        ++stats.page_candidates[cls - 1];
        pages.push_back({cls, weight, key});
    }

    std::sort(
        accounts.begin(), accounts.end(), [](auto const &a, auto const &b) {
            if (a.cls != b.cls) {
                return a.cls < b.cls;
            }
            return std::memcmp(
                       a.address.bytes,
                       b.address.bytes,
                       sizeof(a.address.bytes)) < 0;
        });
    std::sort(pages.begin(), pages.end(), [](auto const &a, auto const &b) {
        if (a.cls != b.cls) {
            return a.cls < b.cls;
        }
        if (a.weight != b.weight) {
            return a.weight < b.weight;
        }
        return std::memcmp(a.key.bytes, b.key.bytes, sizeof(a.key.bytes)) < 0;
    });

    auto &selected_accounts = proposal_post_state_.account_stamps;
    auto &selected_pages = proposal_post_state_.storage_stamps;
    size_t const n_accounts =
        std::min<size_t>(accounts.size(), MAX_ACCOUNT_STAMPS_PER_BLOCK);
    selected_accounts.reserve(n_accounts);
    for (size_t i = 0; i < n_accounts; ++i) {
        selected_accounts.push_back(accounts[i].address);
    }
    stats.account_cap_hit = accounts.size() > n_accounts;
    stats.selected_accounts = n_accounts;
    uint64_t slots = 0;
    for (auto const &p : pages) {
        if (slots + p.weight > MAX_STORAGE_SLOT_STAMPS_PER_BLOCK) {
            stats.page_cap_hit = true;
            break;
        }
        slots += p.weight;
        selected_pages.push_back(p.key);
    }
    stats.selected_pages = selected_pages.size();
    stats.selected_slots = slots;

    // the stamp log record, as storage of STAMP_LOG_ADDRESS: one MIP-8 page
    // leaf per 4 KB chunk in ring slot n mod CACHE_WINDOW_BLOCKS; always
    // written so a stale record never survives in the slot
    byte_string const &record = bytes_alloc_.emplace_back(
        encode_stamp_log_record(n, selected_accounts, selected_pages));
    stats.record_bytes = record.size();
    stats.record_hash = to_bytes(keccak256(record));
    size_t const log_pages = stamp_log_pages(record.size());
    stats.log_pages = log_pages;
    UpdateList page_updates;
    for (size_t i = 0; i < log_pages; ++i) {
        bytes32_t const page_key = stamp_log_page_key(n, i);
        page_updates.push_front(update_alloc_.emplace_back(Update{
            .key = hash_alloc_.emplace_back(
                keccak256({page_key.bytes, sizeof(page_key.bytes)})),
            .value = bytes_alloc_.emplace_back(
                encode_storage_page_db(page_key, stamp_log_page(record, i))),
            .incarnation = false,
            .next = UpdateList{},
            .version = static_cast<int64_t>(n)}));
    }
    Account const log_account{.nonce = 1};
    MONAD_ASSERT(state_update_ != nullptr);
    state_update_->next.push_front(update_alloc_.emplace_back(Update{
        .key = hash_alloc_.emplace_back(keccak256(
            {STAMP_LOG_ADDRESS.bytes, sizeof(STAMP_LOG_ADDRESS.bytes)})),
        .value = bytes_alloc_.emplace_back(
            encode_account_db(STAMP_LOG_ADDRESS, log_account)),
        .incarnation = false,
        .next = std::move(page_updates),
        .version = static_cast<int64_t>(n)}));

    vm::runtime::g_cache_shadow_stats.account_stamp_records.fetch_add(
        n_accounts, std::memory_order_relaxed);
    vm::runtime::g_cache_shadow_stats.storage_stamp_records.fetch_add(
        selected_pages.size(), std::memory_order_relaxed);
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

    push_state_update(std::move(account_updates));
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
