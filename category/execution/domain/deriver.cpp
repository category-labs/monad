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

#include <category/execution/domain/deriver.hpp>

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/core/keccak.hpp>
#include <category/core/result.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/domain/derivation_error.hpp>
#include <category/execution/domain/derive_domain_block.hpp>
#include <category/execution/domain/hpke.hpp>
#include <category/execution/domain/hub_storage.hpp>
#include <category/execution/domain/input_queue.hpp>
#include <category/execution/domain/inputs.hpp>
#include <category/execution/domain/l1_source.hpp>
#include <category/execution/domain/scan_domain_inputs.hpp>
#include <category/execution/domain/spoke.hpp>
#include <category/mpt/db_error.hpp>
#include <category/mpt/util.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>
#include <utility>

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_BEGIN

constexpr std::string_view INPUT_QUEUE_NAMESPACE = "monad.domains.input-queue";

// The hub's latest block of a domain as of an L1 block: its number and the
// L1 block it is derived from. None before the domain is registered.
struct LatestDomainBlock
{
    uint64_t l1_block_number;
    uint64_t number;
};

MONAD_DOMAIN_ANONYMOUS_NAMESPACE_END

MONAD_DOMAIN_NAMESPACE_BEGIN

bytes32_t latest_domain_block_slot(uint64_t const domain_chain_id)
{
    // The queue starts at keccak256(abi.encode(uint64 domainChainId, string
    // INPUT_QUEUE_NAMESPACE)) with its low 7 bits cleared, a page boundary;
    // the latest block is its first slot.
    static_assert(INPUT_QUEUE_NAMESPACE.size() <= 32);
    byte_string encoded(4 * 32, 0);
    store_be(encoded.data() + 24, domain_chain_id);
    encoded[2 * 32 - 1] = 0x40;
    encoded[3 * 32 - 1] = static_cast<uint8_t>(INPUT_QUEUE_NAMESPACE.size());
    std::ranges::copy(INPUT_QUEUE_NAMESPACE, encoded.begin() + 3 * 32);
    bytes32_t slot = to_bytes(keccak256(encoded));
    slot.bytes[31] &= 0x80;
    return slot;
}

Result<DerivationCursor> find_derivation_start(
    L1Source const &l1, Address const &hub, uint64_t const domain_chain_id,
    uint64_t const target)
{
    auto const latest = l1.latest_finalized();
    if (latest == mpt::INVALID_BLOCK_NUM) {
        if (target != 0) {
            return DomainDerivationError::AheadOfHub;
        }
        return DerivationCursor{};
    }

    // The slot is computed once for all the reads.
    auto const read_latest_domain_block =
        [&l1, &hub, slot = latest_domain_block_slot(domain_chain_id)](
            uint64_t const l1_block_number)
        -> Result<std::optional<LatestDomainBlock>> {
        BOOST_OUTCOME_TRY(
            auto const word, l1.read_storage(l1_block_number, hub, slot));
        if (word == bytes32_t{}) {
            return std::optional<LatestDomainBlock>{};
        }
        auto const latest = load_hub_word<LatestBlockWord>(word);
        return std::optional{LatestDomainBlock{
            .l1_block_number = latest.l1_block_number.native(),
            .number = latest.domain_block_number.native()}};
    };

    BOOST_OUTCOME_TRY(auto const tip, read_latest_domain_block(latest));
    uint64_t const hub_next_block = tip.has_value() ? tip->number + 1 : 0;
    if (hub_next_block < target) {
        return DomainDerivationError::AheadOfHub;
    }
    if (hub_next_block == target) {
        // Nothing to derive yet.
        return DerivationCursor{
            .next_l1_block = latest + 1, .next_block = target};
    }

    // The first L1 block at which the hub has recorded block `target`.
    uint64_t low = l1.earliest();
    uint64_t high = latest;
    while (low < high) {
        uint64_t const middle = low + (high - low) / 2;
        BOOST_OUTCOME_TRY(auto const block, read_latest_domain_block(middle));
        if (block.has_value() && block->number >= target) {
            high = middle;
        }
        else {
            low = middle + 1;
        }
    }
    BOOST_OUTCOME_TRY(auto const block, read_latest_domain_block(high));
    // If it is not where the hub recorded block `target`, that L1 block
    // is older than the source's history.
    if (!block.has_value() || block->number != target ||
        block->l1_block_number != high) {
        return mpt::DbError::version_no_longer_exist;
    }
    return DerivationCursor{.next_l1_block = high, .next_block = target};
}

Result<DerivationStart> plan_derivation_start(
    L1Source const &l1, Address const &hub, uint64_t const domain_chain_id,
    uint64_t const next_block)
{
    auto found = find_derivation_start(l1, hub, domain_chain_id, next_block);
    if (found.has_value()) {
        return DerivationStart{
            .source = DerivationStart::Source::Logs,
            .cursor = found.value(),
            .pending = std::nullopt,
            .pending_l1_block = 0};
    }
    if (found.error() != mpt::DbError::version_no_longer_exist) {
        return std::move(found).as_failure();
    }

    // The L1 block of the next block has left the source's history. The hub
    // recorded that block, so the domain is registered and the source has a
    // finalized block.
    uint64_t const l1_block = l1.latest_finalized();
    BOOST_OUTCOME_TRY(
        auto pending,
        read_pending_domain_inputs(l1, hub, domain_chain_id, l1_block));
    if (!pending.has_value()) {
        return DomainDerivationError::MalformedInputQueue;
    }
    auto source = DerivationStart::Source::Pending;
    if (pending->next_block > next_block) {
        // Only an attested checkpoint releases blocks from the queue.
        if (pending->attested_block_hash == bytes32_t{}) {
            return DomainDerivationError::MalformedInputQueue;
        }
        source = DerivationStart::Source::Checkpoint;
    }
    DerivationCursor const cursor{
        .next_l1_block = l1_block + 1,
        .next_block = std::max(next_block, pending->next_block)};
    return DerivationStart{
        .source = source,
        .cursor = cursor,
        .pending = std::move(pending),
        .pending_l1_block = l1_block};
}

PrivateDomainDeriver::PrivateDomainDeriver(
    L1Source const &l1, PrivateDomainKey const &key,
    uint64_t const domain_chain_id, Address const &hub, DerivationCursor cursor)
    : l1_{l1}
    , key_{key}
    , domain_{.chain_id = domain_chain_id, .spoke = DOMAIN_SPOKE}
    , hub_{hub}
    , cursor_{std::move(cursor)}
{
}

Result<bool> PrivateDomainDeriver::derive_next(BlockHandler const &on_block)
{
    auto const finalized = l1_.latest_finalized();
    if (finalized == mpt::INVALID_BLOCK_NUM ||
        finalized < cursor_.next_l1_block) {
        return false;
    }
    // Check header's bloom for domain inputs before reading receipts
    BOOST_OUTCOME_TRY(
        auto const l1_header, l1_.read_finalized_header(cursor_.next_l1_block));
    if (!may_have_domain_inputs(l1_header, hub_, domain_.chain_id)) {
        ++cursor_.next_l1_block;
        return true;
    }
    BOOST_OUTCOME_TRY(
        auto const l1_receipts,
        l1_.read_finalized_receipts(cursor_.next_l1_block));

    BOOST_OUTCOME_TRY(
        auto const inputs,
        scan_domain_inputs(l1_header, l1_receipts, hub_, domain_.chain_id));
    BOOST_OUTCOME_TRY(derive_inputs(inputs, on_block));
    ++cursor_.next_l1_block;
    return true;
}

Result<void> PrivateDomainDeriver::derive_pending(
    PendingDomainInputs const &pending, uint64_t const l1_block_number,
    BlockHandler const &on_block)
{
    // Blocks between the cursor and the first the hub still holds are covered
    // by its checkpoint, and can only be derived from the L1 blocks' logs.
    if (pending.next_block > cursor_.next_block) {
        return DomainDerivationError::BehindCheckpoint;
    }
    // The blocks before the cursor's are already derived.
    uint64_t const derived = cursor_.next_block - pending.next_block;
    if (derived > pending.blocks.size()) {
        return DomainDerivationError::AheadOfHub;
    }
    for (auto i = static_cast<size_t>(derived); i < pending.blocks.size();
         ++i) {
        BOOST_OUTCOME_TRY(derive_inputs(pending.blocks[i], on_block));
    }
    cursor_.next_l1_block = l1_block_number + 1;
    return outcome::success();
}

Result<void> PrivateDomainDeriver::derive_inputs(
    DomainInputs const &inputs, BlockHandler const &on_block)
{
    BOOST_OUTCOME_TRY(
        auto const block,
        derive_domain_block(
            inputs,
            domain_,
            cursor_.next_block,
            [this](byte_string_view const payload) {
                return key_.open_transaction(domain_.chain_id, payload);
            }));
    if (block.has_value()) {
        BOOST_OUTCOME_TRY(on_block(*block));
        cursor_.next_block = block->number + 1;
    }
    return outcome::success();
}

MONAD_DOMAIN_NAMESPACE_END
