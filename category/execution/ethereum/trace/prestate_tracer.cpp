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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/prestate_tracer.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>

#include <nlohmann/json.hpp>

#include <format>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

namespace
{
    using json = nlohmann::json;

    template <size_t N>
    std::string bytes_to_hex(uint8_t const (&input)[N])
    {
        return std::format("0x{}", to_hex(to_byte_string_view(input)));
    }

    std::string byte_string_to_hex(byte_string_view const view)
    {
        return std::format("0x{}", to_hex(view));
    }

    json storage_to_json(AccountState::StorageMap const &storage)
    {
        json res = json::object();
        for (auto const &[key, value] : storage) {
            auto const key_json = bytes_to_hex(key.bytes);
            auto const value_json = bytes_to_hex(value.bytes);
            res[key_json] = value_json;
        }
        return res;
    }

    json account_to_json(std::optional<Account> const &account, State &state)
    {
        json res = json::object();
        if (MONAD_UNLIKELY(!account.has_value())) {
            // If account is created, then only show 'balance = "0x0"'
            res["balance"] = "0x0";
        }
        else {
            res["balance"] =
                std::format("0x{}", to_string(account->balance, 16));
            if (account->code_hash != NULL_HASH) {
                auto const icode =
                    state.read_code(account->code_hash)->intercode();
                res["code"] = byte_string_to_hex(
                    byte_string_view(icode->code(), *icode->code_size()));
            }
            // nonce == 0 is not included in the output.
            if (account->nonce != 0) {
                res["nonce"] = account->nonce; // decimal format
            }
        }
        return res;
    }
}

PrestateTracer::PrestateTracer(
    nlohmann::json &storage, Address const &beneficiary)
    : storage_(storage)
    , beneficiary_(beneficiary)
{
}

void PrestateTracer::operator()(trace::state_trace::State const &op)
{
    state_to_json(
        op.state.original(),
        op.state,
        retain_beneficiary(op.state) ? std::nullopt
                                     : std::optional<Address>{beneficiary_},
        storage_);
}

bool PrestateTracer::retain_beneficiary(State const &state) const
{
    // The following logic determines whether to include the beneficiary in
    // the prestate trace. Since the Shanghai revision, we access the
    // beneficiary before execution, which causes the beneficiary to show up
    // in the prestate trace, even if it did not participate in the block.

    // First check that the beneficiary is in the `original` accounts and
    // `current` accounts. If not, then just return.
    auto const orig_it = state.original().find(beneficiary_);
    auto const curr_it = state.current().find(beneficiary_);
    if (orig_it == state.original().end() || curr_it == state.current().end()) {
        return true;
    }

    OriginalAccountState const &original_state = orig_it->second;
    AccountState const &current_state = curr_it->second.recent();

    // If the original state has no account, then the beneficiary was
    // created during the block and if the current state has an account,
    // then it means that the account is still alive. Thus we must retain it
    // in the prestate trace.
    if (!original_state.has_account() && current_state.has_account()) {
        return true;
    }

    // If neither the original state or the current state have an account,
    // then the beneficiary was created and destroyed during the block,
    // hence we omit it from the prestate trace.
    if (!original_state.has_account() && !current_state.has_account()) {
        return false;
    }

    // If the current state has no account, then the beneficiary was
    // destroyed during the block. Thus we must retain it in the prestate
    // trace.
    if (!current_state.has_account()) {
        return true;
    }

    Account const &original = get_account_for_trace(orig_it->second).value();
    Account const &current =
        get_account_for_trace(curr_it->second.recent()).value();

    // If `original` and `current` are the same and *have* empty storages,
    // then it must be that the beneficiary did not participate in the block
    // and show up here because of the pre-execution access. Therefore we
    // can omit the beneficiary account from the prestate trace.
    if (original == current &&
        // We piggyback on the fact that the `storage_` is lazily populated,
        // i.e. a slot binding appears only if the slot has been read or
        // written to during execution.
        original_state.storage_.empty() && current_state.storage_.empty()) {
        return false;
    }

    // Otherwise the beneficiary must have participate in the block.
    return true;
}

nlohmann::json PrestateTracer::account_state_to_json(
    OriginalAccountState const &as, State &state)
{
    auto const &account = get_account_for_trace(as);
    auto const &storage = as.storage_;
    json res = account_to_json(account, state);
    if (!storage.empty() && account.has_value()) {
        json storage_result = storage_to_json(storage);
        // It is possible for `storage_to_json(storage)` to return an empty
        // object for a non-empty `storage`. It happens when the `storage`
        // contains zero values only.
        if (!storage_result.empty()) {
            res["storage"] = std::move(storage_result);
        }
    }
    return res;
}

void PrestateTracer::state_to_json(
    trace::Map<Address, OriginalAccountState> const &trace, State &state,
    std::optional<Address> const &beneficiary, json &result)
{
    for (auto const &[address, account_state] : trace) {
        // Skip beneficiary account, if present
        if (address == beneficiary) {
            continue;
        }
        // TODO: Because this address is "touched". Should we keep this for
        // monad?
        if (MONAD_UNLIKELY(address == monad::ripemd_address)) {
            continue;
        }
        auto const key = bytes_to_hex(address.bytes);
        result[key] = account_state_to_json(account_state, state);
    }
}

namespace trace
{
    void state_to_json(
        Map<Address, OriginalAccountState> const &trace, State &state,
        std::optional<Address> const &beneficiary, nlohmann::json &result)
    {
        PrestateTracer::state_to_json(trace, state, beneficiary, result);
    }

    nlohmann::json state_to_json(
        Map<Address, OriginalAccountState> const &trace, State &state,
        std::optional<Address> const &beneficiary)
    {
        nlohmann::json result = nlohmann::json::object();
        state_to_json(trace, state, beneficiary, result);
        return result;
    }
}

MONAD_NAMESPACE_END
