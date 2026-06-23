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

#ifdef MONAD_HAVE_ROCKSDB

    #include <category/core/assert.h>
    #include <category/core/byte_string.hpp>
    #include <category/execution/ethereum/db/flat_state_mirror.hpp>
    #include <category/execution/ethereum/db/util.hpp>
    #include <category/statedb/schema.hpp>

    #include <cstdint>
    #include <utility>

MONAD_NAMESPACE_BEGIN

namespace
{
    using statedb::Cf;

    byte_string account_key(Address const &addr)
    {
        return byte_string{addr.bytes, sizeof(addr.bytes)};
    }

    // raw Address (20B) + incarnation (8B, big-endian) + raw slot (32B). The
    // incarnation keeps slots from distinct account lifetimes (selfdestruct +
    // recreate) in separate keys, so a read always sees the live incarnation's
    // value -- matching the trie, whose subtrie is cleared on recreate.
    byte_string storage_key(
        Address const &addr, Incarnation const incarnation,
        bytes32_t const &slot)
    {
        byte_string k;
        k.reserve(sizeof(addr.bytes) + sizeof(uint64_t) + sizeof(slot.bytes));
        k.append(addr.bytes, sizeof(addr.bytes));
        uint64_t const inc = incarnation.to_int();
        for (int shift = 56; shift >= 0; shift -= 8) {
            k.push_back(static_cast<unsigned char>((inc >> shift) & 0xff));
        }
        k.append(slot.bytes, sizeof(slot.bytes));
        return k;
    }
}

std::unique_ptr<FlatStateMirror>
FlatStateMirror::open(std::filesystem::path const &dir)
{
    return std::make_unique<FlatStateMirror>(statedb::KvStore::open(dir));
}

FlatStateMirror::FlatStateMirror(std::unique_ptr<statedb::KvStore> kv)
    : kv_{std::move(kv)}
{
}

void FlatStateMirror::write(StateDeltas const &deltas)
{
    for (auto const &[address, delta] : deltas) {
        auto const &account = delta.account.second;
        // Storage in this block is keyed under the account's live incarnation.
        Incarnation const incarnation =
            account.has_value() ? account->incarnation
                                : (delta.account.first.has_value()
                                       ? delta.account.first->incarnation
                                       : Incarnation{0, 0});

        if (account.has_value()) {
            kv_->put(
                Cf::flat_state,
                account_key(address),
                encode_account_db(address, *account));
        }
        else {
            kv_->erase(Cf::flat_state, account_key(address));
        }

        for (auto const &[slot, storage_delta] : delta.storage) {
            byte_string const sk = storage_key(address, incarnation, slot);
            if (storage_delta.second == bytes32_t{}) {
                kv_->erase(Cf::flat_state, sk);
            }
            else {
                kv_->put(
                    Cf::flat_state,
                    sk,
                    encode_storage_db(slot, storage_delta.second));
            }
        }
    }
}

std::optional<Account> FlatStateMirror::read_account(Address const &addr) const
{
    auto const value = kv_->get(Cf::flat_state, account_key(addr));
    if (!value.has_value()) {
        return std::nullopt;
    }
    byte_string_view encoded{*value};
    return decode_account_db_ignore_address(encoded).value();
}

bytes32_t FlatStateMirror::read_storage(
    Address const &addr, Incarnation const incarnation,
    bytes32_t const &slot) const
{
    auto const value =
        kv_->get(Cf::flat_state, storage_key(addr, incarnation, slot));
    if (!value.has_value()) {
        return {};
    }
    byte_string_view encoded{*value};
    auto const storage = decode_storage_db_ignore_key(encoded);
    MONAD_ASSERT(!storage.has_error());
    return to_bytes(storage.value());
}

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
