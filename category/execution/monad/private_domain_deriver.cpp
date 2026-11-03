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

#include <category/execution/monad/private_domain_deriver.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/execution/monad/private_domain_block_store.hpp>
#include <category/execution/monad/private_domain_derivation.hpp>
#include <category/execution/monad/private_domain_hpke.hpp>
#include <category/execution/monad/private_domain_l1_source.hpp>

#include <boost/outcome/try.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <optional>

MONAD_NAMESPACE_BEGIN

PrivateDomainDeriver::PrivateDomainDeriver(
    L1Source const &l1, DomainBlockStore &store,
    PrivateDomainKeyring const &keyring, Address const &hub,
    uint64_t const start_l1_block)
    : l1_{l1}
    , store_{store}
    , keyring_{keyring}
    , hub_{hub}
    , next_l1_block_{start_l1_block}
{
    MONAD_ASSERT(keyring_.domain_ids().size() == 1);
    if (store_.l1_cursor().has_value()) {
        next_l1_block_ = *store_.l1_cursor() + 1;
    }
    if (store_.tip().has_value()) {
        next_l1_block_ =
            std::max(next_l1_block_, store_.tip()->header.l1_block_number + 1);
    }
}

Result<bool> PrivateDomainDeriver::derive_next()
{
    auto const finalized = l1_.latest_finalized();
    if (!finalized.has_value() || *finalized < next_l1_block_) {
        return false;
    }
    BOOST_OUTCOME_TRY(auto const l1_block, l1_.read_finalized(next_l1_block_));

    uint64_t const domain_chain_id = keyring_.domain_ids().front();
    std::array const states{DomainDerivationState{
        .domain_chain_id = domain_chain_id,
        .spoke = *keyring_.spoke_address(domain_chain_id),
        .latest_header = store_.tip().has_value()
                             ? std::optional{store_.tip()->header}
                             : std::nullopt}};
    BOOST_OUTCOME_TRY(
        auto const derived,
        derive_domain_blocks(
            DomainDerivationInput{
                .l1_header = l1_block.header,
                .l1_block_hash = l1_block.hash,
                .l1_receipts = l1_block.receipts,
                .domain_hub = hub_},
            states,
            [this](uint64_t const id, byte_string_view const payload) {
                return keyring_.open_transaction(id, payload);
            }));
    MONAD_ASSERT(derived.size() <= 1);
    for (auto const &block : derived) {
        store_.append(block.block);
    }
    store_.set_l1_cursor(next_l1_block_);
    ++next_l1_block_;
    return true;
}

MONAD_NAMESPACE_END
