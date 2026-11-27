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

// Hand-built witness blobs and a State fixture for the guest state tests.
// Nodes are appended post-order; each writer returns the id (offset) of the
// node it wrote, and `set_root` must be called last.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/crypto/hash256.h>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/offset_trie.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/code.hpp>
#include <category/vm/vm.hpp>
#include <zkvm/state/key_hash.hpp>
#include <zkvm/state/state.hpp>

#include <array>
#include <cstdint>
#include <cstring>
#include <initializer_list>
#include <memory>
#include <utility>
#include <vector>

namespace monad::zkvm::test
{
    constexpr auto ADDR = 0x00000000000000000000000000000000deadbeef_address;
    constexpr auto OTHER = 0x000000000000000000000000000000000baddcaf_address;

    constexpr auto SLOT_1 =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    constexpr auto SLOT_2 =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    constexpr auto VAL_1 =
        0x000000000000000000000000000000000000000000000000000000000000abcd_bytes32;
    constexpr auto DIGEST =
        0xabababababababababababababababababababababababababababababababab_bytes32;

    constexpr uint64_t BLOCK = 1;
    inline KeySeed const SEED = KeySeed::from_block_hash(
        0x1111111111111111222222222222222233333333333333334444444444444444_bytes32);

    // A key or value whose last byte is `n`.
    inline bytes32_t word(unsigned char const n)
    {
        bytes32_t k{};
        k.bytes[31] = n;
        return k;
    }

    // ---- blob construction -------------------------------------------------

    inline byte_string empty_blob()
    {
        return {'M', 'Z', 'W', 1, 0, 0, 0, 0};
    }

    inline mpt::NodeId here(byte_string const &blob)
    {
        return mpt::NodeId{blob.size()};
    }

    inline void set_root(byte_string &blob, mpt::NodeId const id)
    {
        auto const wire = static_cast<uint32_t>(id);
        std::memcpy(blob.data() + 4, &wire, sizeof(wire));
    }

    inline mpt::NibblesView
    key_path(monad_hash256 const &hash, unsigned const skip)
    {
        return mpt::NibblesView{hash}.substr(skip);
    }

    inline mpt::NodeId put_digest(byte_string &blob)
    {
        auto const id = here(blob);
        mpt::append_digest(blob, DIGEST);
        return id;
    }

    // A storage leaf spelling the whole hashed key, less `skip` nibbles
    // consumed by nodes above it.
    inline mpt::NodeId put_slot(
        byte_string &blob, bytes32_t const &slot, bytes32_t const &value,
        unsigned const skip = 0)
    {
        auto const id = here(blob);
        auto const hash = keccak256(slot.bytes);
        mpt::append_storage(blob, key_path(hash, skip), value);
        return id;
    }

    inline mpt::NodeId put_account(
        byte_string &blob, Address const &addr, Account const &acct,
        mpt::NodeId const storage = mpt::NULL_ID, unsigned const skip = 0)
    {
        auto const id = here(blob);
        auto const hash = keccak256(addr.bytes);
        mpt::append_acct(blob, storage, acct, key_path(hash, skip));
        return id;
    }

    inline mpt::NodeId
    put_branch(byte_string &blob, std::array<mpt::NodeId, 16> const &ch)
    {
        auto const id = here(blob);
        mpt::append_branch(blob, ch);
        return id;
    }

    inline unsigned first_nibble(Address const &addr)
    {
        return keccak256(addr.bytes).bytes[0] >> 4;
    }

    // The account alone, with no storage.
    inline byte_string account_blob(Address const &addr, Account const &acct)
    {
        auto blob = empty_blob();
        set_root(blob, put_account(blob, addr, acct));
        return blob;
    }

    // The account over a one-slot storage trie.
    inline byte_string storage_blob(
        Address const &addr, Account const &acct, bytes32_t const &slot,
        bytes32_t const &value)
    {
        auto blob = empty_blob();
        auto const leaf = put_slot(blob, slot, value);
        set_root(blob, put_account(blob, addr, acct, leaf));
        return blob;
    }

    // The account over a storage trie the witness withholds.
    inline byte_string
    hidden_storage_blob(Address const &addr, Account const &acct)
    {
        auto blob = empty_blob();
        auto const digest = put_digest(blob);
        set_root(blob, put_account(blob, addr, acct, digest));
        return blob;
    }

    // The whole account trie withheld.
    inline byte_string hidden_blob()
    {
        auto blob = empty_blob();
        set_root(blob, put_digest(blob));
        return blob;
    }

    // A root branch with `shown` under its nibble and a digest under
    // `hidden`'s nibble.
    inline byte_string branch_blob(
        Address const &shown, Account const &acct, Address const &hidden)
    {
        MONAD_ASSERT(first_nibble(shown) != first_nibble(hidden));
        auto blob = empty_blob();
        std::array<mpt::NodeId, 16> children{};
        children[first_nibble(hidden)] = put_digest(blob);
        children[first_nibble(shown)] =
            put_account(blob, shown, acct, mpt::NULL_ID, 1);
        set_root(blob, put_branch(blob, children));
        return blob;
    }

    // A root branch with two shown accounts under their nibbles; `a` may
    // carry a one-slot storage trie.
    inline byte_string two_account_blob(
        Address const &a, Account const &acct_a, Address const &b,
        Account const &acct_b, bytes32_t const *const slot_a = nullptr,
        bytes32_t const &value_a = {})
    {
        MONAD_ASSERT(first_nibble(a) != first_nibble(b));
        auto blob = empty_blob();
        std::array<mpt::NodeId, 16> children{};
        mpt::NodeId storage_a = mpt::NULL_ID;
        if (slot_a != nullptr) {
            storage_a = put_slot(blob, *slot_a, value_a);
        }
        children[first_nibble(a)] = put_account(blob, a, acct_a, storage_a, 1);
        children[first_nibble(b)] =
            put_account(blob, b, acct_b, mpt::NULL_ID, 1);
        set_root(blob, put_branch(blob, children));
        return blob;
    }

    // ---- fixture -----------------------------------------------------------

    inline vm::SharedVarcode varcode(std::vector<uint8_t> const &code)
    {
        return std::make_shared<vm::Varcode>(vm::make_shared_intercode(code));
    }

    using CodeTable = State::CodeTable;

    // A code table keyed like the State's: the constructor checks the seed.
    inline CodeTable
    codes(std::initializer_list<CodeTable::value_type> const init = {})
    {
        return CodeTable{init, 0, Bytes32Hash{SEED}};
    }

    // The State holds a view over the blob, so the bytes live here with it.
    struct Fixture
    {
        byte_string blob;
        vm::VM vm;
        State state;

        explicit Fixture(byte_string bytes, CodeTable table = codes())
            : blob{std::move(bytes)}
            , state{mpt::OffsetTrie{blob}, std::move(table), vm, BLOCK, SEED}
        {
        }
    };

    inline std::vector<uint8_t> const CODE{0x60, 0x00, 0x60, 0x00, 0xf3};
    inline bytes32_t const CODE_HASH{
        to_bytes(keccak256(byte_string_view{CODE.data(), CODE.size()}))};
}
