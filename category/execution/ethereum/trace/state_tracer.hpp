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
#include <category/execution/ethereum/trace/tracer_config.h>
#include <category/vm/evm/traits.hpp>

#include <ankerl/unordered_dense.h>
#include <immer/map.hpp>
#include <nlohmann/json_fwd.hpp>

#include <memory>
#include <span>
#include <variant>

MONAD_NAMESPACE_BEGIN

class State;
struct Transaction;

namespace trace
{
    template <typename Key, typename Elem>
    using Map = ankerl::unordered_dense::segmented_map<Key, Elem>;

    template <class Key>
    using Set = ankerl::unordered_dense::set<Key>;

    // PrestateTracer and StateDiffTracer are geth's prestateTracer without
    // and with diffMode. Since diff_mode picks between them, neither reads it.
    struct PrestateTracer
    {
        explicit PrestateTracer(
            nlohmann::json &storage, Address const &beneficiary,
            monad_prestate_tracer_config const &config)
            : storage_(storage)
            , beneficiary_(beneficiary)
            , config_(config)
        {
        }

        PrestateTracer(
            nlohmann::json &, Address const &&,
            monad_prestate_tracer_config const &) = delete;

        void encode(Map<Address, OriginalAccountState> const &, State &);

    private:
        bool retain_beneficiary(State const &state) const;
        static nlohmann::json account_state_to_json(
            OriginalAccountState const &, State &,
            monad_prestate_tracer_config const &);
        static void state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &, nlohmann::json &,
            monad_prestate_tracer_config const &);
        friend void state_to_json(
            Map<Address, OriginalAccountState> const &, State &,
            std::optional<Address> const &, nlohmann::json &,
            monad_prestate_tracer_config const &);
        nlohmann::json &storage_;
        Address const &beneficiary_;
        monad_prestate_tracer_config config_;
    };

    struct StateDiffTracer
    {
        explicit StateDiffTracer(
            nlohmann::json &storage, monad_prestate_tracer_config const &config)
            : storage_(storage)
            , config_(config)
        {
        }

        StateDeltas trace(State const &state);
        void encode(StateDeltas const &, State &);

    private:
        StorageDeltas generate_storage_deltas(
            AccountState::StorageMap const &, AccountState::StorageMap const &);
        nlohmann::json &storage_;
        monad_prestate_tracer_config config_;
    };

    struct AccessListTracer
    {
        AccessListTracer(
            nlohmann::json &storage, Address const &sender,
            Address const &beneficiary, std::optional<Address> const &to,
            std::span<std::optional<Address> const> authorities);

        template <Traits traits>
        void encode(State &);

        void reset();

        // Capture rollback-sensitive accesses from the frame that is about to
        // be rejected. Must be called while that State frame is still pushed.
        void capture_rejected_frame_accesses(State const &);

    private:
        // Merge one account's access metadata into tracer-owned storage.
        void
        capture_accesses(Address const &, AccountState const &account_state);

        // Capture accepted-frame accesses that are still visible in State at
        // final encoding time.
        void capture_accesses(State const &);

        nlohmann::json &storage_;
        Set<Address> excluded_addresses_{};
        Map<Address, Set<bytes32_t>> accesses_{};

        template <Traits traits>
        bool should_exclude_address(Address const &) const;
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

    using StateTracer = std::variant<
        std::monostate, PrestateTracer, StateDiffTracer, AccessListTracer,
        CodeTracer>;

    [[gnu::always_inline]] inline bool is_code_tracer(StateTracer const &tracer)
    {
        return std::holds_alternative<CodeTracer>(tracer);
    }

    inline void on_read_code(
        StateTracer &tracer, bytes32_t const &code_hash,
        vm::SharedIntercode const &intercode)
    {
        if (auto *t = std::get_if<CodeTracer>(&tracer);
            t && code_hash != NULL_HASH) {
            t->codes.emplace(code_hash, intercode);
        }
    }

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
        std::optional<Address> const &,
        monad_prestate_tracer_config const & = {});
    void state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &,
        monad_prestate_tracer_config const &);
    nlohmann::json state_deltas_to_json(
        StateDeltas const &, State &,
        monad_prestate_tracer_config const & = {});
    void state_deltas_to_json(
        StateDeltas const &, State &, nlohmann::json &,
        monad_prestate_tracer_config const &);
}

MONAD_NAMESPACE_END
