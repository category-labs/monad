// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#include "private_domain_execution.hpp"

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/core/likely.h>
#include <category/core/log.hpp>
#include <category/core/rlp/decode_error.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>
#include <category/execution/monad/private_domain_scanner.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/try.hpp>

#include <openssl/crypto.h>

#include <cstddef>
#include <iterator>
#include <memory>
#include <optional>
#include <ranges>
#include <string>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    struct PrivateDomainTransactions
    {
        uint64_t domain_chain_id{};
        std::vector<Transaction> transactions;
        std::vector<uint8_t> within_l1_gas_limit;
    };

    Result<Transaction>
    decode_private_domain_payload(byte_string_view const raw_payload)
    {
        byte_string_view input = raw_payload;
        BOOST_OUTCOME_TRY(auto transaction, rlp::decode_transaction(input));
        if (MONAD_UNLIKELY(!input.empty())) {
            return rlp::DecodeError::InputTooLong;
        }
        return transaction;
    }
}

template <Traits traits>
    requires is_monad_trait_v<traits>
Result<std::vector<PrivateDomainBlockOutput>> execute_private_domain_blocks(
    MonadChain const &chain, Db &db, Db *const secondary_db, vm::VM &vm,
    fiber::PriorityPool &priority_pool,
    BlockHashBuffer const &block_hash_buffer, BlockHeader const &header,
    std::span<Transaction const> const l1_transactions,
    PrivateDomainKeyring const &private_domain_keyring,
    Address const &private_domain_sequencer)
{
    auto const payloads = scan_private_domain_payloads(
        l1_transactions,
        header.number,
        chain.get_chain_id(),
        private_domain_sequencer,
        private_domain_keyring.domain_ids());

    // One L1 block may sequence transactions for several private domains.
    // Preserve payload order within each domain while forming the synthetic
    // blocks that will be executed below.
    std::vector<PrivateDomainTransactions> domain_blocks;
    for (auto const &payload : payloads) {
        auto decrypted = private_domain_keyring.decrypt(
            payload.domain_chain_id, payload.raw_payload);
        if (MONAD_UNLIKELY(decrypted.has_error())) {
            if (decrypted.assume_error() !=
                PrivateDomainHpkeError::DecryptionFailed) {
                return std::move(decrypted).as_failure();
            }
            LOG_WARNING(
                "Dropped private domain payload after decryption failed "
                "in block {} for domain {} at transaction {}",
                header.number,
                payload.domain_chain_id,
                payload.l1_transaction_index);
            continue;
        }

        auto decoded = decode_private_domain_payload(decrypted.value());
        OPENSSL_cleanse(decrypted.value().data(), decrypted.value().size());
        if (MONAD_UNLIKELY(decoded.has_error())) {
            std::string const error = decoded.assume_error().message().c_str();
            LOG_WARNING(
                "Dropped malformed private domain payload in block {} at "
                "transaction {}: {}",
                header.number,
                payload.l1_transaction_index,
                error);
            continue;
        }

        auto block = std::ranges::find_if(
            domain_blocks, [&](PrivateDomainTransactions const &candidate) {
                return candidate.domain_chain_id == payload.domain_chain_id;
            });
        if (block == domain_blocks.end()) {
            domain_blocks.push_back(PrivateDomainTransactions{
                .domain_chain_id = payload.domain_chain_id,
                .transactions = {},
                .within_l1_gas_limit = {}});
            block = std::prev(domain_blocks.end());
        }
        block->within_l1_gas_limit.push_back(
            decoded.value().gas_limit <= payload.l1_gas_limit);
        block->transactions.push_back(std::move(decoded).value());
    }

    std::vector<PrivateDomainBlockOutput> outputs;
    outputs.reserve(payloads.size());

    for (auto &domain_block : domain_blocks) {
        auto &transactions = domain_block.transactions;
        auto const &within_l1_gas_limit = domain_block.within_l1_gas_limit;

        auto recovered_senders = recover_senders(transactions, priority_pool);
        auto recovered_authorities =
            recover_authorities(transactions, priority_pool);

        // Remove failures known from the L1 envelope before constructing the
        // block. Ordinary static and state-dependent transaction validation is
        // deliberately left to execute_block's shared gasless path.
        size_t eligible_count = 0;
        for (size_t i = 0; i < transactions.size(); ++i) {
            if (!within_l1_gas_limit[i] || !recovered_senders[i].has_value() ||
                !transactions[i].sc.chain_id.has_value() ||
                *transactions[i].sc.chain_id != domain_block.domain_chain_id) {
                LOG_WARNING(
                    "Skipped gasless transaction {} for domain {} in "
                    "block {} before execution",
                    i,
                    domain_block.domain_chain_id,
                    header.number);
                continue;
            }
            if (eligible_count != i) {
                transactions[eligible_count] = std::move(transactions[i]);
                recovered_senders[eligible_count] = recovered_senders[i];
                recovered_authorities[eligible_count] =
                    std::move(recovered_authorities[i]);
            }
            ++eligible_count;
        }
        transactions.resize(eligible_count);
        recovered_senders.resize(eligible_count);
        recovered_authorities.resize(eligible_count);

        std::vector<Receipt> receipts;
        DomainStateDeltas domain_deltas;
        Code code;
        if (!transactions.empty()) {
            auto const domain_spoke = private_domain_keyring.spoke_address(
                domain_block.domain_chain_id);
            MONAD_ASSERT(domain_spoke.has_value());
            std::vector<Address> senders;
            senders.reserve(transactions.size());
            std::vector<std::optional<uint64_t>> domains(
                transactions.size(), domain_block.domain_chain_id);
            for (auto const &sender : recovered_senders) {
                MONAD_ASSERT(sender.has_value());
                senders.push_back(*sender);
            }
            auto const senders_and_authorities =
                combine_senders_and_authorities(
                    senders, recovered_authorities, domains);
            AddressesByDomain const empty_history;
            ChainContext<traits> const chain_context{
                .grandparent_senders_and_authorities = empty_history,
                .parent_senders_and_authorities = empty_history,
                .senders_and_authorities = senders_and_authorities,
                .senders = senders,
                .authorities = recovered_authorities,
                .domains = domains};

            std::vector<std::unique_ptr<CallTracerBase>> call_tracers;
            std::vector<std::unique_ptr<trace::StateTracer>> state_tracers;
            call_tracers.reserve(transactions.size());
            state_tracers.reserve(transactions.size());
            for (size_t i = 0; i < transactions.size(); ++i) {
                call_tracers.push_back(std::make_unique<NoopCallTracer>());
                state_tracers.push_back(
                    std::make_unique<trace::StateTracer>(std::monostate{}));
            }

            // Stage into an independent BlockState based on the L1 parent.
            // Nothing reaches the database unless both this execution and the
            // ordinary L1 execution succeed.
            BlockState gasless_state{db, vm, secondary_db};
            BlockMetrics metrics;
            std::vector<uint8_t> skipped_transactions(transactions.size());
            BOOST_OUTCOME_TRY(
                auto execution_receipts,
                execute_block_transactions<traits, true>(
                    chain,
                    header,
                    transactions,
                    recovered_senders,
                    recovered_authorities,
                    gasless_state,
                    block_hash_buffer,
                    priority_pool.fiber_group(),
                    metrics,
                    call_tracers,
                    state_tracers,
                    chain_context,
                    false,
                    skipped_transactions,
                    domain_spoke));

            domain_deltas = gasless_state.release_domain_state_deltas();
            auto [root_deltas, released_code, _] =
                std::move(gasless_state).release();
            MONAD_ASSERT(root_deltas);
            MONAD_ASSERT(root_deltas->empty());
            code = std::move(released_code);

            // Compact validation skips out of the persisted transactions and
            // senders in lockstep. Runtime reverts are retained.
            MONAD_ASSERT(execution_receipts.size() == transactions.size());
            receipts.reserve(execution_receipts.size());
            size_t output_index = 0;
            for (size_t i = 0; i < execution_receipts.size(); ++i) {
                if (!skipped_transactions[i]) {
                    if (output_index != i) {
                        transactions[output_index] = std::move(transactions[i]);
                        recovered_senders[output_index] = recovered_senders[i];
                    }
                    receipts.push_back(std::move(execution_receipts[i]));
                    ++output_index;
                }
            }
            transactions.resize(output_index);
            recovered_senders.resize(output_index);
        }

        MONAD_ASSERT(domain_deltas.empty() || domain_deltas.size() == 1);
        if (!domain_deltas.empty()) {
            DomainStateDeltas::const_accessor it;
            MONAD_ASSERT(domain_deltas.find(it, domain_block.domain_chain_id));
            MONAD_ASSERT(it->second);
        }
        if (transactions.empty()) {
            // Every transaction produced a synthetic zero-gas skip receipt.
            // Discard the isolated BlockState, including speculative deltas.
            continue;
        }
        outputs.push_back(PrivateDomainBlockOutput{
            .domain_chain_id = domain_block.domain_chain_id,
            .state_deltas =
                std::make_unique<DomainStateDeltas>(std::move(domain_deltas)),
            .code = std::make_unique<Code>(std::move(code)),
            .transactions = std::move(transactions),
            .senders = std::move(recovered_senders),
            .receipts = std::move(receipts)});
    }

    return outputs;
}

template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_private_domain_blocks(
    Db &db, Db *const secondary_db, bytes32_t const &block_id,
    BlockHeader const &header,
    std::span<PrivateDomainBlockOutput const> const outputs)
{
    std::vector<PrivateDomainBlockCommitInput> blocks;
    blocks.reserve(outputs.size());
    for (auto const &output : outputs) {
        blocks.push_back(PrivateDomainBlockCommitInput{
            .domain_id = output.domain_chain_id,
            .state_deltas = *output.state_deltas,
            .code = *output.code,
            .transactions = output.transactions,
            .senders = output.senders,
            .receipts = output.receipts});
    }
    commit_private_domain_batch<traits>(
        db, secondary_db, block_id, header, blocks);
}

void validate_domain_state_updates(
    TrieRODb &domain_state_db, std::span<DomainStateUpdate const> const updates)
{
    std::optional<uint64_t> current_block_number;
    bool current_block_available{false};
    for (auto const &update : updates) {
        if (current_block_number != update.domain_block_number) {
            current_block_number = update.domain_block_number;
            try {
                domain_state_db.set_block_and_prefix(*current_block_number);
                current_block_available = true;
            }
            catch (MonadException const &) {
                current_block_available = false;
                LOG_WARNING(
                    "Skipping DomainStateUpdated validation for domain "
                    "{} at block {}: version no longer exists",
                    update.domain_chain_id,
                    update.domain_block_number);
            }
        }
        if (!current_block_available) {
            continue;
        }

        // Newly attested private domain blocks have synthetic headers so
        // validation is independent of the underlying storage encoding.
        // Existing databases do not need historical headers to be backfilled.
        std::optional<BlockHeader> header;
        try {
            header =
                domain_state_db.read_domain_eth_header(update.domain_chain_id);
        }
        catch (MonadException const &) {
            // The version can expire after set_block_and_prefix succeeds.
            // Skip the rest of this version so no update uses a stale cursor.
            current_block_available = false;
            LOG_WARNING(
                "Skipping DomainStateUpdated validation for domain {} "
                "at block {}: version expired during validation",
                update.domain_chain_id,
                update.domain_block_number);
            continue;
        }
        if (!header.has_value()) {
            LOG_WARNING(
                "Skipping DomainStateUpdated validation for domain {} "
                "at block {}: synthetic domain header is unavailable",
                update.domain_chain_id,
                update.domain_block_number);
            continue;
        }
        MONAD_ASSERT_PRINTF(
            header->number == update.domain_block_number,
            "domain header number mismatch for domain %lu: expected "
            "%lu, got %lu",
            update.domain_chain_id,
            update.domain_block_number,
            header->number);
        auto const local = header->state_root;
        MONAD_ASSERT_PRINTF(
            local == update.new_state_root,
            "domain %lu state root mismatch at finalized block %lu: "
            "local=%s attested=%s",
            update.domain_chain_id,
            update.domain_block_number,
            to_hex(to_byte_string_view(local.bytes)).c_str(),
            to_hex(to_byte_string_view(update.new_state_root.bytes)).c_str());
        LOG_INFO(
            "Validated DomainStateUpdated for domain {} at block {}: "
            "state_root={}",
            update.domain_chain_id,
            update.domain_block_number,
            to_hex(to_byte_string_view(update.new_state_root.bytes)));
    }
}

EXPLICIT_MONAD_TRAITS(execute_private_domain_blocks);
EXPLICIT_MONAD_TRAITS(commit_private_domain_blocks);

MONAD_NAMESPACE_END
