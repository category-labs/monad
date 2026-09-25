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

#include <cstdint>
#include <memory>
#include <optional>
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

    struct PrestateTracer
    {
        explicit PrestateTracer(
            nlohmann::json &storage, Address const &beneficiary)
            : storage_(storage)
            , beneficiary_(beneficiary)
        {
        }

        PrestateTracer(nlohmann::json &, Address const &&) = delete;

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

    /// Records what witness generation needs from one transaction's
    /// execution: every code preimage read, keyed by code_hash, and the
    /// lowest block number BLOCKHASH served from the block hash buffer,
    /// which decides how many ancestor headers the witness carries.
    /// Insertions happen from the EVM host; production execution uses
    /// `std::monostate` instead, so the recording path has zero cost.
    ///
    /// The tracer is per transaction and is cleared before every execution
    /// attempt, so a discarded speculative attempt leaves nothing behind and
    /// the block-level merge only sees what the final attempt read. It is
    /// only ever accessed from a single thread, so plain containers suffice.
    struct WitnessTracer
    {
        Map<bytes32_t, vm::SharedIntercode> codes{};
        std::optional<uint64_t> min_block_hash{};
    };

    using StateTracer = std::variant<
        std::monostate, PrestateTracer, StateDiffTracer, AccessListTracer,
        WitnessTracer>;

    [[gnu::always_inline]] inline bool
    is_witness_tracer(StateTracer const &tracer)
    {
        return std::holds_alternative<WitnessTracer>(tracer);
    }

    inline void on_read_code(
        StateTracer &tracer, bytes32_t const &code_hash,
        vm::SharedIntercode const &intercode)
    {
        if (auto *t = std::get_if<WitnessTracer>(&tracer);
            t && code_hash != NULL_HASH) {
            t->codes.emplace(code_hash, intercode);
        }
    }

    inline void on_block_hash(StateTracer &tracer, uint64_t const block_number)
    {
        if (auto *t = std::get_if<WitnessTracer>(&tracer);
            t && (!t->min_block_hash || block_number < *t->min_block_hash)) {
            t->min_block_hash = block_number;
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
        std::optional<Address> const &);
    void state_to_json(
        Map<Address, OriginalAccountState> const &, State &,
        std::optional<Address> const &, nlohmann::json &);
    nlohmann::json state_deltas_to_json(StateDeltas const &, State &);
    void state_deltas_to_json(StateDeltas const &, State &, nlohmann::json &);
}

MONAD_NAMESPACE_END
