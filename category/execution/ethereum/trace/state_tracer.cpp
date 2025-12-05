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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/core/variant.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <nlohmann/json.hpp>

#include <format>
#include <optional>

MONAD_NAMESPACE_BEGIN

namespace trace
{
    using json = nlohmann::json;

    template <std::size_t N>
    std::string bytes_to_hex(uint8_t const (&input)[N])
    {
        return std::format("0x{}", evmc::hex(to_byte_string_view(input)));
    }

    std::string byte_string_to_hex(byte_string_view const view)
    {
        return std::format("0x{}", evmc::hex(view));
    }

    void PrestateTracer::encode(
        Map<Address, OriginalAccountState> const &prestate, State &state)
    {
        state_to_json(prestate, state, storage_);
    }

    StorageDeltas StateDiffTracer::generate_storage_deltas(
        AccountState::StorageMap const &original,
        AccountState::StorageMap const &current)
    {
        StorageDeltas deltas{};
        for (auto const &[key, value] : current) {
            auto const *it = original.find(key);
            MONAD_ASSERT(it != nullptr);
            if (value != *it) {
                deltas.emplace(key, std::make_pair(*it, value));
            }
        }
        return deltas;
    }

    StateDeltas StateDiffTracer::trace(State const &state)
    {
        StateDeltas state_deltas{};

        auto const &current = state.current();
        auto const &original = state.original();

        for (auto const &[address, current_stack] : current) {
            auto const it = original.find(address);
            MONAD_ASSERT(it != original.end());

            // Possible diff.
            auto const &current_account_state = current_stack.recent();
            auto const &current_account =
                get_account_for_trace(current_account_state);
            auto const &current_storage = current_account_state.storage_;
            auto const &original_account_state = it->second;
            auto const &original_account =
                get_account_for_trace(original_account_state);
            auto const &original_storage = original_account_state.storage_;

            // Nothing to do if the account has been created and destructed
            // during the same tx.
            if (!original_account.has_value() && !current_account.has_value()) {
                continue;
            }

            StateDelta state_delta{
                .account = {original_account, current_account},
                .storage =
                    generate_storage_deltas(original_storage, current_storage)};
            state_deltas.emplace(address, std::move(state_delta));
        }
        return state_deltas;
    }

    void StateDiffTracer::encode(StateDeltas const &state_deltas, State &state)
    {
        state_deltas_to_json(state_deltas, state, storage_);
    }

    AccessListTracer::AccessListTracer(
        nlohmann::json &storage, Address const &sender,
        Address const &beneficiary, std::optional<Address> const &to,
        std::span<std::optional<Address> const> const authorities)
        : storage_(storage)
    {
        excluded_addresses_.insert(sender);
        excluded_addresses_.insert(beneficiary);

        if (to.has_value()) {
            excluded_addresses_.insert(*to);
        }

        for (auto const &authority : authorities) {
            if (authority.has_value()) {
                excluded_addresses_.insert(*authority);
            }
        }
    }

    template <Traits traits>
    void AccessListTracer::encode(State &state)
    {
        auto access_list = json::array();
        for (auto const &[address, current_stack] : state.current()) {
            auto keys = json::array();
            auto const &current_account_state = current_stack.recent();
            for (auto const &key :
                 current_account_state.get_accessed_storage()) {
                keys.push_back(bytes_to_hex(key.bytes));
            }

            // If an address is excluded because it's always considered warm, we
            // still want to include it in the access list if it's had storage
            // keys set by this transaction.
            auto const exclude =
                keys.empty() && should_exclude_address<traits>(address);

            if (!exclude) {
                access_list.push_back(json::object({
                    {"address", bytes_to_hex(address.bytes)},
                    {"storageKeys", std::move(keys)},
                }));
            }
        }

        storage_ = std::move(access_list);
    }

    EXPLICIT_TRAITS_MEMBER(AccessListTracer::encode);

    template <Traits traits>
    bool AccessListTracer::should_exclude_address(Address const &addr) const
    {
        return excluded_addresses_.contains(addr) ||
               is_precompile<traits>(addr);
    }

    EXPLICIT_TRAITS_MEMBER(AccessListTracer::should_exclude_address);

    template <Traits traits>
    void run_tracer(StateTracer &tracer, State &state)
    {
        return std::visit(
            overloaded{
                [](std::monostate) {},
                [&state](PrestateTracer &prestate) {
                    prestate.encode(state.original(), state);
                },
                [&state](StateDiffTracer &statediff) {
                    statediff.encode(statediff.trace(state), state);
                },
                [&state](AccessListTracer &access_list) {
                    access_list.encode<traits>(state);
                }},
            tracer);
    }

    EXPLICIT_TRAITS(run_tracer);

    // Json serialization
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
                std::format("0x{}", intx::to_string(account->balance, 16));
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

    json PrestateTracer::account_state_to_json(
        OriginalAccountState const &as, State &state)
    {
        auto const &account = get_account_for_trace(as);
        auto const &storage = as.storage_;
        json res = account_to_json(account, state);
        if (!storage.empty() && account.has_value()) {
            res["storage"] = storage_to_json(storage);
        }
        return res;
    }

    void PrestateTracer::state_to_json(
        Map<Address, OriginalAccountState> const &trace, State &state,
        json &result)
    {
        for (auto const &[address, account_state] : trace) {
            // TODO: Because this address is "touched". Should we keep this for
            // monad?
            if (MONAD_UNLIKELY(address == monad::ripemd_address)) {
                continue;
            }
            auto const key = bytes_to_hex(address.bytes);
            result[key] = account_state_to_json(account_state, state);
        }
    }

    json PrestateTracer::state_to_json(
        Map<Address, OriginalAccountState> const &trace, State &state)
    {
        json result = json::object();
        state_to_json(trace, state, result);
        return result;
    }

    void state_to_json(
        Map<Address, OriginalAccountState> const &trace, State &state,
        json &result)
    {
        PrestateTracer::state_to_json(trace, state, result);
    }

    json
    state_to_json(Map<Address, OriginalAccountState> const &trace, State &state)
    {
        return PrestateTracer::state_to_json(trace, state);
    }

    void state_deltas_to_json(
        StateDeltas const &state_deltas, State &state, json &result)
    {
        json pre = json::object();
        json post = json::object();
        for (auto const &[address, state_delta] : state_deltas) {
            auto const address_key = bytes_to_hex(address.bytes);
            // Account
            {
                auto const &original_account = state_delta.account.first;
                auto const &current_account = state_delta.account.second;

                // Specification (copied from
                // https://geth.ethereum.org/docs/developers/evm-tracing/built-in-tracers)

                // * The accounts in the pre object will still contain all of
                // their basic fields—nonce, balance, and code—even if those
                // fields have not been modified. Storage slots, however, are an
                // exception. Only non-empty slots that have been modified will
                // be included. In other words, if a new slot was written to, it
                // will not appear in the pre object.

                // * The post object is more selective - it only contains the
                // specific fields that were actually modified during the
                // transaction. For example, if only the storage was modified,
                // post will not include unchanged fields like nonce, balance,
                // or code.

                // * Deletion operations are represented by:
                //   - Account selfdestruct: Account appears in pre but not in
                //     post
                //   - Storage clearing (setting a storage value to zero is also
                //     treated as clearing): Storage slot appears in pre but not
                //     in post

                // * Insertion operations are represented by:
                //   - New account creation: Account appears in post but not in
                //     pre
                //   - New storage slot: Storage slot appears in post but not in
                //     pre

                if (!original_account.has_value() &&
                    current_account.has_value()) {
                    // Case: Account created.
                    post[address_key] = account_to_json(current_account, state);
                }
                else if (
                    original_account.has_value() &&
                    !current_account.has_value()) {
                    // Case: Account deleted.
                    pre[address_key] = account_to_json(original_account, state);
                }
                else {
                    // SAFETY: By construction of StateDeltas (assuming they
                    // were constructed by the statediff tracer) cannot contain
                    // the pattern (null, null).
                    MONAD_ASSERT(original_account.has_value());
                    MONAD_ASSERT(current_account.has_value());
                    pre[address_key] = account_to_json(original_account, state);
                    if (original_account->balance != current_account->balance) {
                        post[address_key]["balance"] = std::format(
                            "0x{}",
                            intx::to_string(current_account->balance, 16));
                    }
                    if (original_account->code_hash !=
                        current_account->code_hash) {
                        auto const icode =
                            state.read_code(current_account->code_hash)
                                ->intercode();
                        post[address_key]["code"] =
                            byte_string_to_hex(byte_string_view(
                                icode->code(), *icode->code_size()));
                    }
                    // TODO: Geth has begun including code_hash aswell.
                    if (original_account->nonce != current_account->nonce) {
                        post[address_key]["nonce"] = current_account->nonce;
                    }
                }
            }
            // Storage
            {
                json pre_storage = json::object();
                json post_storage = json::object();
                for (auto const &[key, storage_delta] : state_delta.storage) {
                    auto const key_json = bytes_to_hex(key.bytes);
                    auto const &original_storage = storage_delta.first;
                    auto const &current_storage = storage_delta.second;
                    if (MONAD_LIKELY(original_storage != bytes32_t{})) {
                        pre_storage[key_json] =
                            bytes_to_hex(original_storage.bytes);
                    }
                    if (MONAD_LIKELY(current_storage != bytes32_t{})) {
                        post_storage[key_json] =
                            bytes_to_hex(current_storage.bytes);
                    }
                }
                if (!pre_storage.empty()) {
                    pre[address_key]["storage"] = std::move(pre_storage);
                }
                if (!post_storage.empty()) {
                    post[address_key]["storage"] = std::move(post_storage);
                }
            }
        }
        result["pre"] = std::move(pre);
        result["post"] = std::move(post);
    }

    json state_deltas_to_json(StateDeltas const &state_deltas, State &state)
    {
        json result = json::object();
        state_deltas_to_json(state_deltas, state, result);
        return result;
    }
}

MONAD_NAMESPACE_END
