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

#include <category/execution/ethereum/db/state_delta_log.hpp>

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/hex.hpp>
#include <category/core/int.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/account.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <string>
#include <vector>

MONAD_NAMESPACE_BEGIN

quill::Logger *state_delta_logger = nullptr;

namespace
{
    std::string hex0x(byte_string_view const bytes)
    {
        return "0x" + to_hex(bytes);
    }

    std::string hex0x(Address const &v)
    {
        return "0x" + to_hex(v);
    }

    std::string hex0x(bytes32_t const &v)
    {
        return "0x" + to_hex(v);
    }

    nlohmann::json account_to_json(Account const &acct)
    {
        return nlohmann::json{
            {"balance", "0x" + to_string(acct.balance, 16)},
            {"nonce", fmt::format("0x{:x}", acct.nonce)},
            {"code_hash", hex0x(acct.code_hash)},
            {"incarnation",
             fmt::format("0x{:x}", acct.incarnation.to_int())},
        };
    }

    nlohmann::json
    optional_account_to_json(std::optional<Account> const &acct)
    {
        if (!acct.has_value()) {
            return nullptr;
        }
        return account_to_json(*acct);
    }
}

void log_state_deltas(
    uint64_t const block_number, bytes32_t const &block_hash,
    bytes32_t const &parent_hash, StateDeltas const &state, Code const &code)
{
    if (!state_delta_logger) {
        return;
    }

    // Sort accounts by address for deterministic output. concurrent_hash_map
    // doesn't expose stable iteration order; sorting also makes the produced
    // JSONL diffable across runs.
    std::vector<Address> addrs;
    addrs.reserve(state.size());
    for (auto const &kv : state) {
        addrs.push_back(kv.first);
    }
    std::sort(addrs.begin(), addrs.end());

    nlohmann::json accounts = nlohmann::json::object();
    for (Address const &addr : addrs) {
        StateDeltas::const_accessor it;
        if (!state.find(it, addr)) {
            continue;
        }
        StateDelta const &delta = it->second;

        nlohmann::json entry = nlohmann::json::object();
        entry["pre"] = optional_account_to_json(delta.account.first);
        entry["post"] = optional_account_to_json(delta.account.second);

        std::vector<bytes32_t> slots;
        slots.reserve(delta.storage.size());
        for (auto const &skv : delta.storage) {
            if (skv.second.first != skv.second.second) {
                slots.push_back(skv.first);
            }
        }
        std::sort(slots.begin(), slots.end());

        if (!slots.empty()) {
            nlohmann::json storage = nlohmann::json::object();
            for (bytes32_t const &slot : slots) {
                StorageDeltas::const_accessor sit;
                if (!delta.storage.find(sit, slot)) {
                    continue;
                }
                StorageDelta const &sdelta = sit->second;
                storage[hex0x(slot)] = nlohmann::json{
                    {"pre", hex0x(sdelta.first)},
                    {"post", hex0x(sdelta.second)},
                };
            }
            entry["storage"] = std::move(storage);
        }

        accounts[hex0x(addr)] = std::move(entry);
    }

    std::vector<bytes32_t> code_hashes;
    code_hashes.reserve(code.size());
    for (auto const &kv : code) {
        code_hashes.push_back(kv.first);
    }
    std::sort(code_hashes.begin(), code_hashes.end());

    nlohmann::json code_json = nlohmann::json::object();
    for (bytes32_t const &h : code_hashes) {
        Code::const_accessor it;
        if (!code.find(it, h)) {
            continue;
        }
        auto const &icode = it->second;
        if (!icode || icode->size() == 0) {
            code_json[hex0x(h)] = "0x";
        }
        else {
            code_json[hex0x(h)] =
                hex0x(byte_string_view{icode->code(), icode->size()});
        }
    }

    nlohmann::json block_json{
        {"block", block_number},
        {"block_hash", hex0x(block_hash)},
        {"parent_hash", hex0x(parent_hash)},
        {"accounts", std::move(accounts)},
    };
    if (!code_json.empty()) {
        block_json["code"] = std::move(code_json);
    }

    QUILL_LOG_INFO(state_delta_logger, "{}", block_json.dump());
}

MONAD_NAMESPACE_END
