// Copyright (C) 2026 Category Labs, Inc.
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

#include <zkvm/test/corpus/contracts/token_contracts_bytecode.hpp>
#include <zkvm/test/corpus/token_contracts.hpp>

#include <category/core/assert.h>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>

#include <cstring>
#include <string_view>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

using namespace monad;

byte_string decode(std::string_view const hex)
{
    auto code = from_hex(hex);
    MONAD_ASSERT(code.has_value());
    return std::move(code).value();
}

byte_string call(uint32_t const selector)
{
    byte_string out;
    for (unsigned i = 0; i < 4; ++i) {
        out.push_back(static_cast<unsigned char>(selector >> (24 - 8 * i)));
    }
    return out;
}

void push(byte_string &out, bytes32_t const &w)
{
    out.append(w.bytes, sizeof(w.bytes));
}

/// keccak256(key ‖ base): a mapping's slot for `key`, where `base` is the
/// mapping's own slot -- or, one level down, the slot the outer key led to.
bytes32_t mapping_slot(bytes32_t const &key, bytes32_t const &base)
{
    byte_string buf;
    push(buf, key);
    push(buf, base);
    return to_bytes(keccak256(buf));
}

/// Payment is a static tuple, so abi.encode lays it out inline: eight words,
/// no offsets, and calldata carries exactly the same words after the
/// selector.
byte_string payment_words(corpus::tokens::Payment const &p)
{
    using corpus::tokens::word;
    byte_string out;
    push(out, word(p.ref));
    push(out, word(p.token_a));
    push(out, word(p.debtor));
    push(out, word(p.intermediary));
    push(out, word(p.amount_a));
    push(out, word(p.token_b));
    push(out, word(p.creditor));
    push(out, word(p.amount_b));
    return out;
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

namespace corpus::tokens
{
    byte_string const &wrapped_token_code()
    {
        static byte_string const code = decode(WRAPPED_TOKEN_RUNTIME_HEX);
        return code;
    }

    byte_string const &pvp_settlement_code()
    {
        static byte_string const code = decode(PVP_SETTLEMENT_RUNTIME_HEX);
        return code;
    }

    byte_string const &earn_vault_code()
    {
        static byte_string const code = decode(EARN_VAULT_RUNTIME_HEX);
        return code;
    }

    bytes32_t word(uint256_t const &v)
    {
        return store_be_as<bytes32_t>(v);
    }

    bytes32_t word(Address const &a)
    {
        bytes32_t w{};
        std::memcpy(w.bytes + 12, a.bytes, sizeof(a.bytes));
        return w;
    }

    bytes32_t balance_slot(Address const &holder)
    {
        return mapping_slot(word(holder), word(uint256_t{0}));
    }

    bytes32_t allowance_slot(Address const &owner, Address const &spender)
    {
        return mapping_slot(
            word(spender), mapping_slot(word(owner), word(uint256_t{1})));
    }

    byte_string transfer(Address const &to, uint256_t const &value)
    {
        auto out = call(abi_encode_selector("transfer(address,uint256)"));
        push(out, word(to));
        push(out, word(value));
        return out;
    }

    byte_string batch_transfer(
        std::vector<Address> const &to, std::vector<uint256_t> const &value)
    {
        MONAD_ASSERT(to.size() == value.size());
        auto out =
            call(abi_encode_selector("batchTransfer(address[],uint256[])"));
        // Two dynamic arrays: two head offsets, then each tail as a length
        // and its words. The second tail starts after the first's length
        // word and its n elements.
        size_t const n = to.size();
        push(out, word(uint256_t{0x40}));
        push(out, word(uint256_t{0x40 + 32 * (n + 1)}));
        push(out, word(uint256_t{n}));
        for (auto const &a : to) {
            push(out, word(a));
        }
        push(out, word(uint256_t{n}));
        for (auto const &v : value) {
            push(out, word(v));
        }
        return out;
    }

    byte_string withdraw_to_l1(uint256_t const &value, Address const &l1_to)
    {
        auto out = call(abi_encode_selector("withdrawToL1(uint256,address)"));
        push(out, word(value));
        push(out, word(l1_to));
        return out;
    }

    byte_string set_eligible(Address const &holder, bool const ok)
    {
        auto out = call(abi_encode_selector("setEligible(address,bool)"));
        push(out, word(holder));
        push(out, word(uint256_t{ok ? 1u : 0u}));
        return out;
    }

    bytes32_t vault_verified_slot(Address const &owner)
    {
        return mapping_slot(word(owner), word(uint256_t{1}));
    }

    bytes32_t vault_shares_slot(Address const &owner)
    {
        return mapping_slot(word(owner), word(uint256_t{2}));
    }

    byte_string vault_deposit(uint256_t const &assets)
    {
        auto out = call(abi_encode_selector("deposit(uint256)"));
        push(out, word(assets));
        return out;
    }

    byte_string vault_withdraw(uint256_t const &assets)
    {
        auto out = call(abi_encode_selector("withdraw(uint256)"));
        push(out, word(assets));
        return out;
    }

    bytes32_t payment_id(Payment const &p)
    {
        return to_bytes(keccak256(payment_words(p)));
    }

    bytes32_t pvp_pending_slot(bytes32_t const &id)
    {
        return mapping_slot(id, word(uint256_t{0}));
    }

    byte_string propose(Payment const &p)
    {
        auto out = call(abi_encode_selector(
            "propose((uint256,address,address,address,uint256,address,address,"
            "uint256))"));
        out += payment_words(p);
        return out;
    }

    byte_string settle(Payment const &p)
    {
        auto out = call(abi_encode_selector(
            "settle((uint256,address,address,address,uint256,address,address,"
            "uint256))"));
        out += payment_words(p);
        return out;
    }
}

MONAD_NAMESPACE_END
