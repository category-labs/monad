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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/db/commit_builder.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/db/page_commit_builder.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/traits.hpp>

MONAD_NAMESPACE_BEGIN

template <Traits traits>
    requires is_monad_trait_v<traits>
DomainStateRoots commit_private_domain_batch(
    Db &primary_db, Db *const secondary_db, bytes32_t const &block_id,
    BlockHeader const &header,
    std::span<PrivateDomainBlockCommitInput const> const blocks)
{
    if (blocks.empty()) {
        return {};
    }

    // Each private domain block is executed independently, so it produces a
    // separate DomainStateDeltas map containing at most one domain.
    std::vector<DomainStateDeltas const *> state_delta_sets;
    Code code;
    std::vector<std::vector<Address>> db_senders;
    std::vector<DomainBlockAncillaries> ancillaries;
    state_delta_sets.reserve(blocks.size());
    db_senders.reserve(blocks.size());
    ancillaries.reserve(blocks.size());

    for (auto const &block : blocks) {
        MONAD_ASSERT(block.transactions.size() == block.senders.size());
        MONAD_ASSERT(block.transactions.size() == block.receipts.size());
        state_delta_sets.push_back(&block.state_deltas);
        for (auto const &[domain, _] : block.state_deltas) {
            MONAD_ASSERT(domain == block.domain_id);
        }
        for (auto const &[hash, intercode] : block.code) {
            code.emplace(hash, intercode);
        }

        auto &senders = db_senders.emplace_back();
        senders.reserve(block.senders.size());
        for (auto const &sender : block.senders) {
            senders.push_back(sender.value_or(Address{}));
        }
        ancillaries.push_back(DomainBlockAncillaries{
            .domain_id = block.domain_id,
            .transactions = block.transactions,
            .senders = senders,
            .receipts = block.receipts});
    }

    auto add_block = [&](CommitBuilder &builder) {
        builder.add_domain_state_deltas(state_delta_sets, true)
            .add_code(code)
            .add_domain_block_ancillaries(ancillaries);
    };
    auto const make_domain_headers = [&](DomainStateRoots const &roots) {
        std::vector<std::pair<uint64_t, BlockHeader>> headers;
        headers.reserve(roots.size());
        for (auto const &[domain_id, state_root] : roots) {
            headers.emplace_back(
                domain_id,
                BlockHeader{.state_root = state_root, .number = header.number});
        }
        return headers;
    };

    if (secondary_db == nullptr) {
        MONAD_ASSERT(primary_db.is_page_encoded() == traits::mip_8_active());
        auto builder = make_commit_builder(header.number, primary_db);
        add_block(*builder);
        return primary_db.commit_domain_state_deltas(
            block_id,
            *builder,
            state_delta_sets,
            header.number,
            [&](CommitBuilder &header_builder, DomainStateRoots const &roots) {
                auto const headers = make_domain_headers(roots);
                header_builder.add_domain_block_headers(headers);
            });
    }

    MONAD_ASSERT(
        !primary_db.is_page_encoded() && secondary_db->is_page_encoded());
    auto builder = make_commit_builder(header.number, primary_db);
    add_block(*builder);
    auto builder2 = make_commit_builder(header.number, *secondary_db);
    add_block(*builder2);

    bool const primary_is_canonical = !traits::mip_8_active();
    // Match commit_block's root selection exactly: slot-primary before MIP-8,
    // page-secondary after MIP-8. The selected root is then recorded in both
    // timelines so finalized validation only needs the ordinary primary RODb.
    DomainStateRoots canonical_roots;
    std::vector<std::pair<uint64_t, BlockHeader>> canonical_headers;
    auto const populate_canonical_headers =
        [&](CommitBuilder &header_builder,
            DomainStateRoots const &local_roots) {
            canonical_roots = local_roots;
            canonical_headers = make_domain_headers(canonical_roots);
            header_builder.add_domain_block_headers(canonical_headers);
        };
    auto const populate_noncanonical_headers =
        [&](CommitBuilder &header_builder, DomainStateRoots const &) {
            header_builder.add_domain_block_headers(canonical_headers);
        };
    if (primary_is_canonical) {
        auto roots = primary_db.commit_domain_state_deltas(
            block_id,
            *builder,
            state_delta_sets,
            header.number,
            populate_canonical_headers);
        secondary_db->commit_domain_state_deltas(
            block_id,
            *builder2,
            state_delta_sets,
            header.number,
            populate_noncanonical_headers);
        return roots;
    }
    auto roots = secondary_db->commit_domain_state_deltas(
        block_id,
        *builder2,
        state_delta_sets,
        header.number,
        populate_canonical_headers);
    primary_db.commit_domain_state_deltas(
        block_id,
        *builder,
        state_delta_sets,
        header.number,
        populate_noncanonical_headers);
    return roots;
}

template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_block(
    Db &primary_db, Db *const secondary_db, bytes32_t const &block_id,
    BlockHeader const &header, StateDeltas const &state,
    BlockCommitAncillaries const &anc)
{
    auto add_common_deltas = [&](CommitBuilder &b) {
        b.add_code(anc.code)
            .add_receipts(anc.receipts)
            .add_transactions(anc.transactions, anc.senders)
            .add_call_frames(anc.call_frames)
            .add_ommers(anc.ommers);
        if (anc.withdrawals.has_value()) {
            b.add_withdrawals(anc.withdrawals.value());
        }
    };

    // `canonical_db` is the "source of truth" Db the header populator reads
    // roots from. Both commits call populate_header via this same pointer, so
    // both dbs end up with identical block headers. The pointer is assigned
    // just before the commits run. Non-state roots are the same on both dbs, so
    // the choice only really changes which state_root is stamped into the
    // header.
    Db *canonical_db = nullptr;
    auto populate_header = [&](BlockHeader &h) {
        MONAD_ASSERT(canonical_db != nullptr);
        h.receipts_root = canonical_db->receipts_root();
        h.state_root = canonical_db->state_root();
        h.withdrawals_root = canonical_db->withdrawals_root();
        h.transactions_root = canonical_db->transactions_root();
        h.gas_used = anc.receipts.empty() ? 0 : anc.receipts.back().gas_used;
        h.logs_bloom = compute_bloom(anc.receipts);
        h.ommers_hash = compute_ommers_hash(anc.ommers);
    };

    if (secondary_db == nullptr) {
        MONAD_ASSERT(primary_db.is_page_encoded() == traits::mip_8_active());
        auto builder = make_commit_builder(header.number, primary_db);
        builder->add_state_deltas(state);
        add_common_deltas(*builder);
        canonical_db = &primary_db;
        primary_db.commit(block_id, *builder, header, state, populate_header);
        return;
    }

    // Dual-write migration path. The primary and secondary dbs write the same
    // data to every table; the only difference is state encoding. state_deltas
    // is added separately to each builder so the page builder's override can
    // kick in; everything else goes through the shared helper.
    MONAD_ASSERT(
        !primary_db.is_page_encoded() && secondary_db->is_page_encoded());
    auto builder = make_commit_builder(header.number, primary_db);
    builder->add_state_deltas(state);
    add_common_deltas(*builder);

    auto builder2 = make_commit_builder(header.number, *secondary_db);
    builder2->add_state_deltas(state);
    add_common_deltas(*builder2);

    // The canonical db owns the state_root stamped into the header: pre-fork
    // the slot-encoded primary, post-fork (mip-8 active) the page-encoded
    // secondary. The canonical db commits first so its roots are live when the
    // other db's populate_header runs.
    bool const primary_is_canonical = !traits::mip_8_active();
    canonical_db = primary_is_canonical ? &primary_db : secondary_db;
    if (primary_is_canonical) {
        primary_db.commit(block_id, *builder, header, state, populate_header);
        secondary_db->commit(
            block_id, *builder2, header, state, populate_header);
    }
    else {
        secondary_db->commit(
            block_id, *builder2, header, state, populate_header);
        primary_db.commit(block_id, *builder, header, state, populate_header);
    }
}

EXPLICIT_MONAD_TRAITS(commit_private_domain_batch);
EXPLICIT_MONAD_TRAITS(commit_block);

MONAD_NAMESPACE_END
