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

#pragma once

#include <category/core/bytes.hpp>
#include <category/core/runtime/unaligned.hpp>
#include <category/execution/domain/config.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>

MONAD_DOMAIN_NAMESPACE_BEGIN

// The words of the DomainHub's storage that the client reads, as the hub
// packs them: fields from the high bytes to the low bytes, integers
// big-endian. See InputQueue.sol in category-labs/monad-domains.

// A domain's latest block, the first word of its input queue: zero until the
// domain is registered.
struct LatestBlockWord
{
    u64_be gas_sold;
    u64_be input_words;
    u64_be l1_block_number;
    u64_be domain_block_number;
};

static_assert(sizeof(LatestBlockWord) == sizeof(bytes32_t));

// Reads the storage word `word` as a `Word`.
template <typename Word>
    requires(sizeof(Word) == sizeof(bytes32_t))
Word load_hub_word(bytes32_t const &word)
{
    return unaligned_load<Word>(word.bytes);
}

MONAD_DOMAIN_NAMESPACE_END
