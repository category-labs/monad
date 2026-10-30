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

#include <category/execution/monad/private_domains.hpp>

#include <category/core/assert.h>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/monad/core/rlp/domain_block_rlp.hpp>

#include <boost/outcome/try.hpp>

#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

PrivateDomainBlocks::PrivateDomainBlocks(std::vector<DerivedDomainBlock> blocks)
    : blocks_{std::move(blocks)}
    , derived_{true}
{
    encoded_headers_.reserve(blocks_.size());
    commits_.reserve(blocks_.size());
    for (auto const &derived : blocks_) {
        auto const &header = derived.block.header;
        encoded_headers_.push_back(rlp::encode_proposed_domain_header(header));
        commits_.push_back(DomainBlockCommit{
            .domain_chain_id = header.domain_chain_id,
            .number = header.number,
            .encoded_header = encoded_headers_.back(),
            .transactions = derived.block.transactions,
            .senders = derived.senders});
    }
}

Result<PrivateDomainBlocks> derive_private_domain_blocks(
    PrivateDomains const *const domains, Db &parent_db,
    BlockHeader const &l1_header, bytes32_t const &l1_block_id,
    std::span<Receipt const> const l1_receipts)
{
    if (domains == nullptr) {
        return PrivateDomainBlocks{};
    }
    if (domains->keyring.domain_ids().empty()) {
        return PrivateDomainBlocks{std::vector<DerivedDomainBlock>{}};
    }

    std::vector<DomainDerivationState> states;
    for (auto const domain_chain_id : domains->keyring.domain_ids()) {
        DomainDerivationState state{
            .domain_chain_id = domain_chain_id,
            .spoke = *domains->keyring.spoke_address(domain_chain_id)};
        if (auto const encoded =
                parent_db.read_domain_block_header(domain_chain_id)) {
            byte_string_view view{*encoded};
            auto header = rlp::decode_proposed_domain_header(view);
            MONAD_ASSERT_PRINTF(
                header.has_value() && view.empty(),
                "corrupt header of private domain %lu",
                domain_chain_id);
            state.latest_header = std::move(header.value());
        }
        states.push_back(std::move(state));
    }

    BOOST_OUTCOME_TRY(
        auto blocks,
        derive_domain_blocks(
            DomainDerivationInput{
                .l1_header = l1_header,
                .l1_block_id = l1_block_id,
                .l1_receipts = l1_receipts,
                .domain_hub = domains->hub},
            states,
            [&](uint64_t const domain_chain_id,
                byte_string_view const payload) {
                return domains->keyring.open_transaction(
                    domain_chain_id, payload);
            }));
    return PrivateDomainBlocks{std::move(blocks)};
}

MONAD_NAMESPACE_END
