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

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/lru/static_lru_cache.hpp>
#include <category/core/monad_exception.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/rpc/lazy_block_hash.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

LazyBlockHash::LazyBlockHash(mpt::RODb const &db, uint64_t const n)
    : db_{db}
    , n_{n}
    , blockhash_cache_{N}
{
}

uint64_t LazyBlockHash::n() const
{
    return n_;
}

bytes32_t const &LazyBlockHash::get(uint64_t const n) const
{
    MONAD_ASSERT_PRINTF(n < n_ && n + N >= n_, "n_=%lu, n=%lu", n_, n);
    if (Cache::ConstAccessor acc; blockhash_cache_.find(acc, n)) {
        return acc->second->val;
    }

    auto const cursor_res = db_.find(
        mpt::concat(FINALIZED_NIBBLE, mpt::NibblesView{block_header_nibbles}),
        n);
    MONAD_ASSERT_THROW(!cursor_res.has_error(), "blockhash: error querying DB");
    bytes32_t const blockhash =
        to_bytes(keccak256(cursor_res.value().node->value()));
    auto const res = blockhash_cache_.insert(n, blockhash);
    return res.first->second->val;
}

MONAD_NAMESPACE_END
