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

#include "monad_cli_domain.hpp"

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/trie_rodb.hpp>
#include <category/execution/monad/core/domain_block.hpp>
#include <category/execution/monad/core/rlp/domain_block_rlp.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/ondisk_db_config.hpp>

#include <nlohmann/json.hpp>

#include <cstdint>
#include <filesystem>
#include <iostream>

MONAD_NAMESPACE_BEGIN

namespace
{
    ProposedDomainHeader decode_domain_header(byte_string const &encoded)
    {
        byte_string_view view{encoded};
        auto header = rlp::decode_proposed_domain_header(view);
        MONAD_ASSERT(header.has_value() && view.empty());
        return header.value();
    }
}

int dump_domain_blocks(
    std::filesystem::path const &dbname_path, uint64_t const version,
    uint64_t const domain_chain_id)
{
    mpt::RODb rodb{mpt::ReadOnlyOnDiskDbConfig{.dbname_path = dbname_path}};
    TrieRODb at_version{rodb};
    at_version.set_block_and_prefix(version);
    auto const latest = at_version.read_domain_block_header(domain_chain_id);
    if (!latest.has_value()) {
        return 0;
    }
    auto const hex = [](byte_string_view const bytes) {
        return "0x" + to_hex(bytes);
    };
    uint64_t const latest_number = decode_domain_header(*latest).number;
    for (uint64_t number = 0; number <= latest_number; ++number) {
        auto const l1_block_number =
            at_version.read_domain_block_l1_number(domain_chain_id, number);
        if (!l1_block_number.has_value()) {
            // Expired from the index.
            std::cout
                << nlohmann::json{{"number", number}, {"expired", true}}.dump()
                << '\n';
            continue;
        }
        TrieRODb at_block{rodb};
        at_block.set_block_and_prefix(*l1_block_number);
        auto const header = decode_domain_header(
            at_block.read_domain_block_header(domain_chain_id).value());
        MONAD_ASSERT(header.number == number);
        nlohmann::json transactions = nlohmann::json::array();
        for (auto const &[tx, sender] :
             at_block.read_domain_transactions(domain_chain_id)) {
            transactions.push_back(
                {{"encoded", hex(rlp::encode_transaction(tx))},
                 {"sender", hex(to_byte_string_view(sender.bytes))}});
        }
        nlohmann::json const block{
            {"domain_chain_id", header.domain_chain_id},
            {"number", header.number},
            {"l1_block_number", header.l1_block_number},
            {"l1_block_id", hex(to_byte_string_view(header.l1_block_id.bytes))},
            {"timestamp", header.timestamp},
            {"mix_hash", hex(to_byte_string_view(header.mix_hash.bytes))},
            {"gas_limit", header.gas_limit},
            {"base_fee_per_gas", to_string(header.base_fee_per_gas, 10)},
            {"transactions_root",
             hex(to_byte_string_view(header.transactions_root.bytes))},
            {"transactions", std::move(transactions)}};
        std::cout << block.dump() << '\n';
    }
    return 0;
}

MONAD_NAMESPACE_END
