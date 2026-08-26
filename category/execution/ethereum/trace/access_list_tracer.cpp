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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/trace/access_list_tracer.hpp>
#include <category/execution/ethereum/trace/state_trace_operations.hpp>
#include <category/execution/monad/db/storage_page.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <nlohmann/json.hpp>

#include <algorithm>
#include <format>
#include <ranges>
#include <span>
#include <utility>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace
{
    template <size_t N>
    std::string bytes_to_hex(uint8_t const (&input)[N])
    {
        return std::format("0x{}", to_hex(to_byte_string_view(input)));
    }
}

AccessListTracer::AccessListTracer(
    nlohmann::json &storage, Address const &sender,
    Address const &beneficiary, std::optional<Address> const &to,
    std::span<std::optional<Address> const> const authorities,
    bool const dedup_storage_pages, IsPrecompileFn const is_precompile)
    : storage_(storage)
    , dedup_storage_pages_(dedup_storage_pages)
    , is_precompile_(is_precompile)
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

void AccessListTracer::capture_accesses(
    Address const &address, AccountState const &account_state)
{
    auto &storage_keys = accesses_[address];
    for (auto const &key : account_state.get_accessed_storage()) {
        storage_keys.insert(key);
    }
}

void AccessListTracer::capture_accesses(State const &state)
{
    for (auto const &[address, current_stack] : state.current()) {
        capture_accesses(address, current_stack.recent());
    }
}

void AccessListTracer::capture_rejected_frame_accesses(State const &state)
{
    auto const &current = state.current();
    for (auto const &address : state.current_frame_dirty_accounts()) {
        auto const it = current.find(address);
        MONAD_ASSERT(it != current.end());
        capture_accesses(address, it->second.recent());
    }
}

bool AccessListTracer::should_exclude_address(Address const &addr) const
{
    return excluded_addresses_.contains(addr) ||
           (is_precompile_ && is_precompile_(addr));
}

void AccessListTracer::encode(State const &state)
{
    // Merge accepted-frame accesses still visible in State with any
    // failed-frame accesses captured before rollback.
    capture_accesses(state);

    struct AccessListEntry
    {
        Address address;
        std::vector<bytes32_t> storage_keys;
    };

    std::vector<AccessListEntry> entries;
    entries.reserve(accesses_.size());
    for (auto const &[address, storage_keys] : accesses_) {
        auto &entry = entries.emplace_back();
        entry.address = address;
        // Match go-ethereum's access-list tracer output order: storage
        // keys are sorted within each address, then entries are sorted by
        // address below.
        entry.storage_keys.assign(storage_keys.begin(), storage_keys.end());
        std::ranges::sort(entry.storage_keys);
        if (dedup_storage_pages_) {
            // Under page-gas (MIP-8), warming one slot warms all 128 slots
            // on its page, so keep only one representative per page.
            auto const dups = std::ranges::unique(
                entry.storage_keys, {}, compute_page_key);
            entry.storage_keys.erase(dups.begin(), dups.end());
        }
    }
    std::ranges::sort(entries, {}, &AccessListEntry::address);

    auto access_list = nlohmann::json::array();
    for (auto const &[address, storage_keys] : entries) {
        // If an address is excluded because it's always considered warm, we
        // still include it when there are warmed storage keys.
        if (storage_keys.empty() && should_exclude_address(address)) {
            continue;
        }

        auto keys = nlohmann::json::array();
        for (auto const &key : storage_keys) {
            keys.push_back(bytes_to_hex(key.bytes));
        }

        access_list.push_back(nlohmann::json::object({
            {"address", bytes_to_hex(address.bytes)},
            {"storageKeys", std::move(keys)},
        }));
    }

    storage_ = std::move(access_list);
}

void AccessListTracer::operator()(trace::state_trace::State const &op)
{
    encode(op.state);
}

void AccessListTracer::operator()(trace::state_trace::RejectFrame const &op)
{
    capture_rejected_frame_accesses(op.state);
}

void AccessListTracer::operator()(trace::state_trace::Reset const &)
{
    accesses_.clear();
}

template <Traits traits>
void AccessListTracer::encode(State &state)
{
    auto const prev_dedup_storage_pages = dedup_storage_pages_;
    auto const prev_is_precompile = is_precompile_;
    dedup_storage_pages_ = traits::mip_8_active();
    is_precompile_ = &is_precompile<traits>;
    encode(static_cast<State const &>(state));
    dedup_storage_pages_ = prev_dedup_storage_pages;
    is_precompile_ = prev_is_precompile;
}

EXPLICIT_TRAITS_MEMBER(AccessListTracer::encode);

MONAD_NAMESPACE_END
