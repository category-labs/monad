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
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/chain/monad_chain.hpp>
#include <category/execution/monad/db/commit_block_migration.hpp>
#include <category/execution/monad/private_domain_fee.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>
#include <category/execution/monad/private_domain_scanner.hpp>
#include <category/execution/monad/private_domain_system_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <boost/outcome/try.hpp>

#include <openssl/crypto.h>

#include <algorithm>
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
    // An L1DomainMessage with its target resolved, decrypted if encrypted.
    struct L1MessageDelivery
    {
        uint64_t source_chain_id{};
        Address from{};
        Address to{};
        byte_string data{};
        uint256_t nonce{};
        uint64_t gas_limit{};
    };

    struct PrivateDomainTransactions
    {
        uint64_t domain_chain_id{};
        std::vector<Transaction> transactions;
        std::vector<L1MessageDelivery> deliveries;
    };

    // An encrypted message plaintext is `to[20] || data`.
    constexpr size_t MESSAGE_TARGET_SIZE = sizeof(Address);

    PrivateDomainTransactions &find_or_create_domain_block(
        std::vector<PrivateDomainTransactions> &domain_blocks,
        uint64_t const domain_chain_id)
    {
        auto block = std::ranges::find_if(
            domain_blocks, [&](PrivateDomainTransactions const &candidate) {
                return candidate.domain_chain_id == domain_chain_id;
            });
        if (block == domain_blocks.end()) {
            domain_blocks.push_back(
                PrivateDomainTransactions{.domain_chain_id = domain_chain_id});
            block = std::prev(domain_blocks.end());
        }
        return *block;
    }

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
    std::span<Receipt const> const l1_receipts,
    PrivateDomainKeyring const &private_domain_keyring,
    Address const &domain_hub)
{
    // Only the hub emits these events from its address, so a malformed one
    // means the configured hub contract is incompatible with this client.
    auto scanned_transactions = scan_sequenced_domain_transactions(
        l1_receipts, domain_hub, private_domain_keyring.domain_ids());
    MONAD_ASSERT_PRINTF(
        scanned_transactions.has_value(),
        "malformed sequencing event from domain hub: %s",
        scanned_transactions.assume_error().message().c_str());
    auto scanned_messages = scan_l1_domain_messages(
        l1_receipts, domain_hub, private_domain_keyring.domain_ids());
    MONAD_ASSERT_PRINTF(
        scanned_messages.has_value(),
        "malformed L1 message event from domain hub: %s",
        scanned_messages.assume_error().message().c_str());

    // Group by domain, preserving event order.
    std::vector<PrivateDomainTransactions> domain_blocks;
    for (auto const &sequenced : scanned_transactions.value()) {
        auto decrypted = private_domain_keyring.decrypt(
            sequenced.domain_chain_id, sequenced.payload);
        if (MONAD_UNLIKELY(decrypted.has_error())) {
            if (decrypted.assume_error() !=
                PrivateDomainHpkeError::DecryptionFailed) {
                return std::move(decrypted).as_failure();
            }
            LOG_WARNING(
                "Dropped private domain payload after decryption failed "
                "in block {} for domain {} at transaction {}",
                header.number,
                sequenced.domain_chain_id,
                sequenced.l1_transaction_index);
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
                sequenced.l1_transaction_index,
                error);
            continue;
        }

        uint64_t const purchased_gas =
            purchased_domain_gas(sequenced.fee, header.gas_limit);
        if (decoded.value().gas_limit > purchased_gas) {
            LOG_WARNING(
                "Dropped underpaid private domain transaction in block {} at "
                "transaction {}: gas limit {} exceeds the {} gas its fee bought",
                header.number,
                sequenced.l1_transaction_index,
                decoded.value().gas_limit,
                purchased_gas);
            continue;
        }

        find_or_create_domain_block(domain_blocks, sequenced.domain_chain_id)
            .transactions.push_back(std::move(decoded).value());
    }

    // Deliveries follow their domain's sequenced transactions in hub nonce
    // order. An encrypted message that does not decrypt or lacks a 20-byte
    // target is dropped; the spoke accepts the nonce gap.
    for (auto &message : scanned_messages.value()) {
        L1MessageDelivery delivery{
            .source_chain_id = message.source_chain_id,
            .from = message.from,
            .to = {},
            .data = {},
            .nonce = message.nonce,
            .gas_limit = purchased_domain_gas(message.fee, header.gas_limit)};
        if (message.encrypted) {
            auto decrypted = private_domain_keyring.decrypt(
                message.domain_chain_id, message.payload);
            if (MONAD_UNLIKELY(decrypted.has_error())) {
                if (decrypted.assume_error() !=
                    PrivateDomainHpkeError::DecryptionFailed) {
                    return std::move(decrypted).as_failure();
                }
                LOG_WARNING(
                    "Dropped encrypted L1 message {} for domain {} in "
                    "block {} at transaction {}: decryption failed",
                    to_string(message.nonce),
                    message.domain_chain_id,
                    header.number,
                    message.l1_transaction_index);
                continue;
            }
            auto &plaintext = decrypted.value();
            if (MONAD_UNLIKELY(plaintext.size() < MESSAGE_TARGET_SIZE)) {
                OPENSSL_cleanse(plaintext.data(), plaintext.size());
                LOG_WARNING(
                    "Dropped encrypted L1 message {} for domain {} in "
                    "block {} at transaction {}: plaintext too short for a "
                    "target address",
                    to_string(message.nonce),
                    message.domain_chain_id,
                    header.number,
                    message.l1_transaction_index);
                continue;
            }
            std::copy_n(
                plaintext.data(), MESSAGE_TARGET_SIZE, delivery.to.bytes);
            delivery.data.assign(
                plaintext.data() + MESSAGE_TARGET_SIZE,
                plaintext.size() - MESSAGE_TARGET_SIZE);
            OPENSSL_cleanse(plaintext.data(), plaintext.size());
        }
        else {
            MONAD_ASSERT(message.to.has_value());
            delivery.to = *message.to;
            delivery.data = std::move(message.payload);
        }
        find_or_create_domain_block(domain_blocks, message.domain_chain_id)
            .deliveries.push_back(std::move(delivery));
    }

    std::vector<PrivateDomainBlockOutput> outputs;
    outputs.reserve(domain_blocks.size());

    for (auto &domain_block : domain_blocks) {
        auto &transactions = domain_block.transactions;
        auto const &deliveries = domain_block.deliveries;

        auto recovered_senders = recover_senders(transactions, priority_pool);
        auto recovered_authorities =
            recover_authorities(transactions, priority_pool);

        // Envelope checks (signature, chain id, reserved relayer); everything
        // else is left to execute_block's shared validation.
        size_t eligible_count = 0;
        for (size_t i = 0; i < transactions.size(); ++i) {
            if (!recovered_senders[i].has_value() ||
                *recovered_senders[i] == DOMAIN_SYSTEM_RELAYER ||
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
        if (!transactions.empty() || !deliveries.empty()) {
            auto const domain_spoke = private_domain_keyring.spoke_address(
                domain_block.domain_chain_id);
            MONAD_ASSERT(domain_spoke.has_value());

            // Stage into an independent BlockState based on the L1 parent.
            // Nothing reaches the database unless both this execution and the
            // ordinary L1 execution succeed.
            BlockState gasless_state{db, vm, secondary_db};

            if (!deliveries.empty()) {
                // Only derived deliveries advance the relayer nonce; continue
                // from the parent domain state.
                uint64_t relayer_nonce = [&] {
                    State probe{
                        gasless_state,
                        Incarnation{header.number, 0},
                        false,
                        domain_block.domain_chain_id};
                    return probe.get_nonce(DOMAIN_SYSTEM_RELAYER);
                }();
                for (auto const &delivery : deliveries) {
                    auto transaction = make_domain_system_transaction(
                        domain_block.domain_chain_id,
                        *domain_spoke,
                        relayer_nonce,
                        header.base_fee_per_gas.value_or(0),
                        delivery.gas_limit,
                        delivery.source_chain_id,
                        delivery.from,
                        delivery.to,
                        delivery.data,
                        delivery.nonce);
                    // Pre-validate so a delivery the shared static validation
                    // would skip does not consume a relayer nonce and break
                    // every later delivery; its hub nonce becomes a gap.
                    auto const validation =
                        static_validate_transaction<traits, true>(
                            transaction,
                            header.base_fee_per_gas,
                            header.excess_blob_gas,
                            chain.get_chain_id(),
                            chain.get_blob_schedule(header.timestamp));
                    if (MONAD_UNLIKELY(validation.has_error())) {
                        LOG_WARNING(
                            "Dropped undeliverable L1 message {} for "
                            "domain {} in block {}: {}",
                            to_string(delivery.nonce),
                            domain_block.domain_chain_id,
                            header.number,
                            validation.assume_error().message().c_str());
                        continue;
                    }
                    ++relayer_nonce;
                    transactions.push_back(std::move(transaction));
                    recovered_senders.push_back(DOMAIN_SYSTEM_RELAYER);
                    recovered_authorities.emplace_back();
                }
            }

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
                    /* exec_recorder = */ nullptr,
                    /* trace_transfers = */ false,
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
            // Every transaction produced a synthetic zero-gas skip receipt, or
            // nothing survived the envelope checks. Discard the isolated
            // BlockState, including speculative deltas.
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
                // The hub accepts any block newer than its commitment, so an
                // attestation can reach this node before it has finalized
                // that block; the finalized root is not known yet then.
                current_block_available =
                    domain_state_db.try_set_block_and_prefix(
                        *current_block_number);
                if (!current_block_available) {
                    LOG_WARNING(
                        "Skipping DomainStateUpdated validation for domain "
                        "{} at block {}: block is not finalized locally",
                        update.domain_chain_id,
                        update.domain_block_number);
                }
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
        // An attestation that disagrees with local history is reported, not
        // treated as fatal: the hub has already accepted it, and this check
        // only tells the operator that the validators and this node diverge.
        if (header->number != update.domain_block_number) {
            LOG_ERROR(
                "domain {} header number mismatch at finalized block {}: "
                "local={} attested={}",
                update.domain_chain_id,
                update.domain_block_number,
                header->number,
                update.domain_block_number);
            continue;
        }
        auto const local = header->state_root;
        if (local != update.new_state_root) {
            LOG_ERROR(
                "domain {} state root mismatch at finalized block {}: "
                "local={} attested={}",
                update.domain_chain_id,
                update.domain_block_number,
                to_hex(to_byte_string_view(local.bytes)),
                to_hex(to_byte_string_view(update.new_state_root.bytes)));
            continue;
        }
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
