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

#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/chain/patch_output_header.hpp>
#include <category/execution/ethereum/core/block.hpp>

#include <evmc/evmc.h>

MONAD_NAMESPACE_BEGIN

void patch_output_header(
    Chain const &chain, BlockHeader const &input_header,
    BlockHeader &output_header)
{
    auto const rev =
        chain.get_revision(output_header.number, output_header.timestamp);
    if (rev <= EVMC_BYZANTIUM) {
        // TODO: TrieDb does not calculate receipts root correctly before the
        // BYZANTIUM fork. However, for empty receipts our receipts root
        // calculation is correct.
        //
        // On monad, the receipts root input is always null. On replay, we set
        // our receipts root to any non-null header input so our eth header is
        // correct in the Db.
        output_header.withdrawals_root = input_header.withdrawals_root;
    }
}

MONAD_NAMESPACE_END
