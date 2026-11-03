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

// Db backed by a witness-derived partial trie (see offset_trie.hpp).

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/code.hpp>

#include <ankerl/unordered_dense.h>

#include <cstdint>
#include <optional>
#include <utility>

MONAD_NAMESPACE_BEGIN

using CodeIndex = ankerl::unordered_dense::map<bytes32_t, vm::SharedIntercode>;

class PartialTrieDb final
{
    mpt::OffsetTrie trie_;
    CodeIndex codes_;
    uint64_t block_number_{0};

public:
    PartialTrieDb(mpt::OffsetTrie trie, CodeIndex codes)
        : trie_(std::move(trie))
        , codes_(std::move(codes))
    {
    }

public:
    PartialTrieDb() = delete;

    bytes32_t read_storage(Address const &, Incarnation, bytes32_t const &);

    // Outer nullopt means unresolved witness data; an engaged outer optional
    // containing nullopt is a proven absence. Never cache the former as empty.
    std::optional<std::optional<Account>>
    try_read_account(Address const &address)
    {
        auto const key = keccak256(address.bytes);
        auto const node =
            trie_.try_find_original(trie_.root, mpt::NibblesView{key});
        if (!node) {
            return std::nullopt;
        }
        auto account = match(
            *node,
            Cases{
                [](mpt::NullView) -> std::optional<Account> {
                    return std::nullopt;
                },
                [](mpt::AccountLeafView leaf) -> std::optional<Account> {
                    return leaf.account();
                },
                [](auto) -> std::optional<Account> {
                    MONAD_ABORT("incorrect node type in account read");
                }});
        return std::optional<std::optional<Account>>{
            std::in_place, std::move(account)};
    }

    std::optional<bytes32_t>
    try_read_storage(Address const &address, bytes32_t const &slot)
    {
        auto const akey = keccak256(address.bytes);
        auto const node =
            trie_.try_find_original(trie_.root, mpt::NibblesView{akey});
        if (!node) {
            return std::nullopt;
        }
        auto const storage = match(
            *node,
            Cases{
                [](mpt::NullView) { return mpt::NULL_ID; },
                [](mpt::AccountLeafView leaf) { return leaf.storage(); },
                [](auto) -> mpt::NodeId {
                    MONAD_ABORT("incorrect node type in storage account read");
                }});
        if (storage == mpt::NULL_ID) {
            return bytes32_t{};
        }
        auto const skey = keccak256(slot.bytes);
        auto const value =
            trie_.try_find_original(storage, mpt::NibblesView{skey});
        if (!value) {
            return std::nullopt;
        }
        return match(
            *value,
            Cases{
                [](mpt::NullView) { return bytes32_t{}; },
                [](mpt::StorageLeafView leaf) { return leaf.value(); },
                [](auto) -> bytes32_t {
                    MONAD_ABORT("incorrect node type in storage read");
                }});
    }

    vm::SharedIntercode read_code(bytes32_t const &code_hash)
    {
        auto const it = codes_.find(code_hash);
        return it == codes_.end() ? vm::make_shared_intercode({}) : it->second;
    }

    bytes32_t state_root()
    {
        return trie_.state_root();
    }

    uint64_t get_block_number() const
    {
        return block_number_;
    }

    void set_block_and_prefix(uint64_t const block_number, bytes32_t const &)
    {
        block_number_ = block_number;
    }

    void commit(BlockHeader const &, StateDeltas const &);
};

MONAD_NAMESPACE_END
