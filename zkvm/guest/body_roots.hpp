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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>

#include <span>
#include <vector>

MONAD_NAMESPACE_BEGIN

//! Root of an Ethereum ordered trie: item i stored under key rlp(i). This is
//! the shape of the transactions, receipts and withdrawals tries, and it is
//! what binds the block BODY the guest executed to the header whose hash is a
//! public value. The empty trie returns NULL_ROOT.
bytes32_t ordered_trie_root(std::span<byte_string_view const> items);

//! Convenience overload for callers holding owned buffers.
bytes32_t ordered_trie_root(std::vector<byte_string> const &items);

MONAD_NAMESPACE_END
