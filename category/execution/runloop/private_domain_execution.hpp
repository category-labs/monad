// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

#pragma once

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>
#include <category/execution/monad/private_domain_scanner.hpp>
#include <category/vm/evm/traits.hpp>

#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

class BlockHashBuffer;
class TrieRODb;
struct Db;
struct BlockHeader;
struct MonadChain;

struct PrivateDomainBlockOutput
{
    uint64_t domain_chain_id{};
    std::unique_ptr<DomainStateDeltas> state_deltas;
    std::unique_ptr<Code> code;
    std::vector<Transaction> transactions;
    std::vector<std::optional<Address>> senders;
    std::vector<Receipt> receipts;
};

namespace fiber
{
    class PriorityPool;
}

namespace vm
{
    class VM;
}

template <Traits traits>
    requires is_monad_trait_v<traits>
Result<std::vector<PrivateDomainBlockOutput>> execute_private_domain_blocks(
    MonadChain const &, Db &, Db *secondary_db, vm::VM &, fiber::PriorityPool &,
    BlockHashBuffer const &, BlockHeader const &,
    std::span<Transaction const> l1_transactions,
    PrivateDomainKeyring const &private_domain_keyring,
    Address const &private_domain_sequencer);

template <Traits traits>
    requires is_monad_trait_v<traits>
void commit_private_domain_blocks(
    Db &, Db *secondary_db, bytes32_t const &block_id, BlockHeader const &,
    std::span<PrivateDomainBlockOutput const>);

void validate_domain_state_updates(
    TrieRODb &domain_state_db, std::span<DomainStateUpdate const>);

MONAD_NAMESPACE_END
