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

#include <zkvm/state/account_state.hpp>

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/cases.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>

MONAD_NAMESPACE_BEGIN

namespace zkvm
{
    namespace
    {
        bytes32_t const ZERO{};
    }

    bool AccountState::stamp_is_live(SlotState const &s) const
    {
        return account_.has_value() && s.incarnation == account_->incarnation;
    }

    bool
    AccountState::resolve_slot(SlotState &s, mpt::OffsetTrie const &trie) const
    {
        s.key_hash = to_bytes(keccak256(s.key.bytes));
        if (storage_root != mpt::NULL_ID) {
            auto const found =
                trie.try_find_original(storage_root, key_path(s.key_hash));
            if (!found.has_value()) {
                return false;
            }
            mpt::match(
                *found,
                Cases{
                    [](mpt::NullView) {},
                    [&](mpt::StorageLeafView const l) {
                        s.block_start = l.value();
                    },
                    [](auto) {
                        MONAD_ABORT(
                            "zkvm State: storage walk ended off a leaf");
                    }});
        }
        s.resolved = true;
        return true;
    }

    bytes32_t const *AccountState::try_current_value(
        SlotState &s, mpt::OffsetTrie const &trie) const
    {
        if (s.written) {
            return stamp_is_live(s) ? &s.current : &ZERO;
        }
        // The account was created or re-created in this block: the witness
        // value is gone.
        if (account_->incarnation != WITNESS_INCARNATION) {
            return &ZERO;
        }
        if (!s.resolved && MONAD_UNLIKELY(!resolve_slot(s, trie))) {
            return nullptr;
        }
        return &s.block_start;
    }

    bytes32_t const &
    AccountState::current_value(SlotState &s, mpt::OffsetTrie const &trie) const
    {
        bytes32_t const *const value = try_current_value(s, trie);
        if (MONAD_UNLIKELY(value == nullptr)) {
            MONAD_ABORT("zkvm State: storage slot not in the witness");
        }
        return *value;
    }

    bytes32_t const &AccountState::tx_original_value(
        SlotState &s, mpt::OffsetTrie const &trie) const
    {
        if (s.written) {
            return stamp_is_live(s) ? s.tx_start : ZERO;
        }
        // Unwritten this block: the slot reads as it did when the
        // transaction began.
        return current_value(s, trie);
    }
}

MONAD_NAMESPACE_END
