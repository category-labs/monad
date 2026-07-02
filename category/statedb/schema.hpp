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

#pragma once

#include <category/core/config.hpp>

#include <array>
#include <cstddef>
#include <cstdint>
#include <string_view>

MONAD_NAMESPACE_BEGIN

namespace statedb
{
    // The four RocksDB column families backing the state store.
    //
    //   flat_state : raw Address [+ slot/page key] -> account /
    //                storage value (decode_account_db_raw / storage_page_t),
    //                serving read_account/read_storage without trie traversal.
    //   code       : code_hash (32B) -> raw bytecode.
    //   trie_nodes : trie path -> serialized trie node, keyed by the node's
    //                position (account nodes: 0x00 ++ nibble-path; storage
    //                nodes: 0x01 ++ account-path ++ nibble-path), so a changed
    //                node overwrites its own key and the CF stays in trie
    //                order. The node's RLP still carries child hashes (with
    //                <32B children inlined); a 1-byte prune-epoch tag is
    //                appended. Used only for the state root, proofs, and
    //                statesync.
    //   meta       : fixed string keys -> finalized/verified/voted/proposed
    //                pointers, per-retained-block state_root + root node_hash,
    //                the retained_roots window, prune.epoch, and
    //                schema.version. Receipts / transactions / withdrawals
    //                roots are stored here per block (not as separate flat CFs,
    //                to avoid split-brain).
    enum class Cf : std::size_t
    {
        flat_state = 0,
        code,
        trie_nodes,
        meta,
    };

    inline constexpr std::size_t NUM_CF = 4;

    // RocksDB column-family names, indexed by static_cast<std::size_t>(Cf).
    inline constexpr std::array<std::string_view, NUM_CF> CF_NAMES{
        "flat_state", "code", "trie_nodes", "meta"};

    inline constexpr std::string_view cf_name(Cf const cf) noexcept
    {
        return CF_NAMES[static_cast<std::size_t>(cf)];
    }

    // Bumped when the on-disk layout changes; persisted under CF_META.
    inline constexpr std::uint32_t SCHEMA_VERSION = 1;

    // Fixed CF_META keys. F2 wires none of these yet (keep-all pruning: the
    // prune.epoch key exists in the schema but is unused until F13/Phase 2).
    namespace meta_key
    {
        inline constexpr std::string_view schema_version = "schema.version";
        inline constexpr std::string_view finalized = "finalized";
        // Per-retained-block state root (F8 seed writes block N's; the retained
        // window grows in later PRs).
        inline constexpr std::string_view state_root = "state_root";
        inline constexpr std::string_view verified = "verified";
        inline constexpr std::string_view voted = "voted";
        inline constexpr std::string_view proposed = "proposed";
        inline constexpr std::string_view prune_epoch = "prune.epoch";
    }
}

MONAD_NAMESPACE_END
