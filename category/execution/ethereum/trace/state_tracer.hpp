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

#pragma once

#include <category/core/address.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/account_state.hpp>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>
#include <immer/map.hpp>
#include <nlohmann/json_fwd.hpp>

#include <memory>
#include <variant>

MONAD_NAMESPACE_BEGIN

class State;
struct Transaction;

namespace trace
{
    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    struct PrestateTracer
    {
        explicit PrestateTracer(
            nlohmann::json &storage, Address const &beneficiary)
            : storage_(storage)
            , beneficiary_(beneficiary)
        {
        }

        void encode(Map<Address, OriginalAccountState> const &, State &);

    private:
        bool retain_beneficiary(State const &state) const;
        static nlohmann::json
        account_state_to_json(OriginalAccountState const &, State &);
        static void state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &, nlohmann::json &);
        static nlohmann::json state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &);
        friend void state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &, nlohmann::json &);
        friend nlohmann::json state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &);
        nlohmann::json &storage_;
        Address const &beneficiary_;
    };

    struct StateDiffTracer
    {
        explicit StateDiffTracer(nlohmann::json &storage)
            : storage_(storage)
        {
        }

        StateDeltas trace(State const &state);
        void encode(StateDeltas const &, State &);

    private:
        StorageDeltas generate_storage_deltas(
            AccountState::StorageMap const &, AccountState::StorageMap const &);
        nlohmann::json &storage_;
    };

    /// Records every code preimage read during execution, keyed by
    /// code_hash. Used by witness generation to assemble the codes section
    /// of the post-block witness. Insertions happen from the EVM host's
    /// code-read entry points; production execution uses `std::monostate`
    /// instead, so the recording path has zero cost. A CodeTracer is only
    /// ever accessed from a single thread, so a plain (non-concurrent) map
    /// suffices.
    struct CodeTracer
    {
        Map<bytes32_t, vm::SharedIntercode> codes{};
    };

    using StateTracer =
        std::variant<std::monostate, PrestateTracer, StateDiffTracer>;

    // State-tracer lifecycle hook for a failed frame. Call immediately before
    // State::pop_reject(), while rejected-frame access metadata is still
    // visible through State.
    void on_frame_reject(StateTracer &, State &);

    // Clear execution-attempt-local tracer state before speculative execution.
    void reset(StateTracer &);

    // Finalise and serialise tracer output after transaction execution, once
    // accepted-frame state has been merged into the visible State view.
    template <Traits traits>
    void run_tracer(StateTracer &tracer, State &state);

    nlohmann::json state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &);
    void state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &);
    nlohmann::json state_deltas_to_json(StateDeltas const &, State &);
    void state_deltas_to_json(StateDeltas const &, State &, nlohmann::json &);
}

MONAD_NAMESPACE_END
