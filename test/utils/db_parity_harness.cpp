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

#include "db_parity_harness.hpp"

#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/db.hpp>
#include <category/vm/code.hpp>

#include <optional>
#include <span>
#include <string>
#include <utility>

MONAD_TEST_NAMESPACE_BEGIN

namespace
{
    std::string hex(std::span<unsigned char const> const bytes)
    {
        static constexpr char digits[] = "0123456789abcdef";
        std::string s;
        s.reserve(2 + bytes.size() * 2);
        s += "0x";
        for (unsigned char const b : bytes) {
            s += digits[b >> 4];
            s += digits[b & 0x0f];
        }
        return s;
    }

    std::string hex(bytes32_t const &b)
    {
        return hex(std::span<unsigned char const>{b.bytes, sizeof(b.bytes)});
    }

    std::string hex(Address const &a)
    {
        return hex(std::span<unsigned char const>{a.bytes, sizeof(a.bytes)});
    }

    std::string opt_hex(std::optional<bytes32_t> const &b)
    {
        return b.has_value() ? hex(*b) : std::string{"(none)"};
    }

    bool code_equal(vm::SharedIntercode const &a, vm::SharedIntercode const &b)
    {
        if (static_cast<bool>(a) != static_cast<bool>(b)) {
            return false;
        }
        if (!a) {
            return true;
        }
        return byte_string_view{a->code(), a->size()} ==
               byte_string_view{b->code(), b->size()};
    }
}

DbParityHarness::DbParityHarness(
    Db &reference, Db &candidate, std::string reference_label,
    std::string candidate_label)
    : reference_{reference}
    , candidate_{candidate}
    , reference_label_{std::move(reference_label)}
    , candidate_label_{std::move(candidate_label)}
{
}

BlockParity DbParityHarness::compare(
    uint64_t const number, std::span<SampledKey const> const sampled)
{
    BlockParity result{.number = number};

    auto const diff = [&result, this](
                          char const *const what,
                          std::string const &ref,
                          std::string const &cand) {
        if (ref != cand) {
            result.mismatches.push_back(
                std::string{what} + ": " + reference_label_ + "=" + ref + " " +
                candidate_label_ + "=" + cand);
        }
    };

    diff(
        "state_root",
        hex(reference_.state_root()),
        hex(candidate_.state_root()));
    diff(
        "receipts_root",
        hex(reference_.receipts_root()),
        hex(candidate_.receipts_root()));
    diff(
        "transactions_root",
        hex(reference_.transactions_root()),
        hex(candidate_.transactions_root()));
    diff(
        "withdrawals_root",
        opt_hex(reference_.withdrawals_root()),
        opt_hex(candidate_.withdrawals_root()));

    for (SampledKey const &k : sampled) {
        switch (k.kind) {
        case SampledKey::Kind::account: {
            if (reference_.read_account(k.address) !=
                candidate_.read_account(k.address)) {
                result.mismatches.push_back(
                    "account[" + hex(k.address) + "] differs");
            }
            break;
        }
        case SampledKey::Kind::storage: {
            auto const r = reference_.read_storage(
                k.address, k.incarnation, k.slot_or_code_hash);
            auto const c = candidate_.read_storage(
                k.address, k.incarnation, k.slot_or_code_hash);
            if (r != c) {
                result.mismatches.push_back(
                    "storage[" + hex(k.address) + ":" +
                    hex(k.slot_or_code_hash) + "]: " + reference_label_ + "=" +
                    hex(r) + " " + candidate_label_ + "=" + hex(c));
            }
            break;
        }
        case SampledKey::Kind::code: {
            if (!code_equal(
                    reference_.read_code(k.slot_or_code_hash),
                    candidate_.read_code(k.slot_or_code_hash))) {
                result.mismatches.push_back(
                    "code[" + hex(k.slot_or_code_hash) + "] differs");
            }
            break;
        }
        }
    }

    ++blocks_;
    if (!result.match()) {
        ++mismatched_blocks_;
    }
    return result;
}

BlockParity DbParityHarness::on_block(
    uint64_t const number, std::function<void(Db &)> const &commit_one,
    std::span<SampledKey const> const sampled)
{
    commit_one(reference_);
    commit_one(candidate_);
    return compare(number, sampled);
}

MONAD_TEST_NAMESPACE_END
