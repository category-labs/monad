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

    #include <rocksdb/iterator.h>
    #include <rocksdb/slice.h>

    #include <cstdint>
    #include <cstring>
    #include <utility>
    #include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    using statedb::Cf;

    byte_string account_key(Address const &addr)
    {
        return byte_string{addr.bytes, sizeof(addr.bytes)};
    }

    // raw Address (20B) + raw slot (32B). Account deletion / incarnation bumps
    // explicitly clear all storage keys for the address before new live slots are
    // written.
    byte_string storage_key(Address const &addr, bytes32_t const &slot)
    {
        byte_string k;
        k.reserve(sizeof(addr.bytes) + sizeof(slot.bytes));
        k.append(addr.bytes, sizeof(addr.bytes));
        k.append(slot.bytes, sizeof(slot.bytes));
        return k;
    }

    byte_string storage_seek_key(Address const &addr)
    {
        byte_string k{addr.bytes, sizeof(addr.bytes)};
        k.push_back(0);
        return k;
    }

    rocksdb::Slice to_slice(byte_string_view const v)
    {
        return rocksdb::Slice{
            reinterpret_cast<char const *>(v.data()), v.size()};
    }

    bool is_storage_key_for_address(
        rocksdb::Slice const &key, Address const &addr)
    {
        return key.size() > sizeof(addr.bytes) &&
               std::memcmp(key.data(), addr.bytes, sizeof(addr.bytes)) == 0;
    }

    byte_string to_byte_string(rocksdb::Slice const &key)
    {
        return byte_string{
            reinterpret_cast<unsigned char const *>(key.data()), key.size()};
    }

    void erase_storage_for_address(
        statedb::KvStore &kv, Address const &addr)
    {
        std::vector<byte_string> keys;
        auto it = kv.new_iterator(Cf::flat_state);
        byte_string const start = storage_seek_key(addr);
        for (it->Seek(to_slice(start)); it->Valid(); it->Next()) {
            rocksdb::Slice const key = it->key();
            if (!is_storage_key_for_address(key, addr)) {
                break;
            }
            keys.push_back(to_byte_string(key));
        }
        MONAD_ASSERT(it->status().ok());
        for (byte_string const &key : keys) {
            kv.erase(Cf::flat_state, key);
        }
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
        bool const account_deleted =
            !account.has_value() && delta.account.first.has_value();
        bool const inc_bump =
            account.has_value() && delta.account.first.has_value() &&
            delta.account.first->incarnation != account->incarnation;

        if (account.has_value()) {
            kv_->put(
                Cf::flat_state,
                account_key(address),
                encode_account_db(address, *account));
        }
        else {
            kv_->erase(Cf::flat_state, account_key(address));
        }
        if (account_deleted || inc_bump) {
            erase_storage_for_address(*kv_, address);
        }
        if (!account.has_value()) {
            continue;
        }

        for (auto const &[slot, storage_delta] : delta.storage) {
            byte_string const sk = storage_key(address, slot);
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
    Address const &addr, Incarnation const, bytes32_t const &slot) const
{
    auto const value = kv_->get(Cf::flat_state, storage_key(addr, slot));
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
