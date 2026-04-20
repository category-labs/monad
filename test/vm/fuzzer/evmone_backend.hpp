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

#include "fuzzer_backend.hpp"

#include "state.hpp"
#include "test_state.hpp"

#include <evmc/evmc.hpp>

namespace monad::vm::fuzzing
{
    /// FuzzerBackend implemented over evmone's state types.
    /// Takes an evmc::VM at construction — the VM is the only thing that
    /// varies between the reference and subject sides of the differential
    /// test. Construct a new instance per run; there is no reset().
    class EvmoneBackend : public FuzzerBackend
    {
        evmc::VM vm_;
        evmone::test::TestState initial_;
        evmone::state::State state_;

        static evmone::test::TestState
        make_initial_state(std::span<GenesisAccount const> genesis);

    public:
        EvmoneBackend(evmc::VM vm, std::span<GenesisAccount const> genesis);

        // Non-movable: state_ holds a reference to the sibling initial_ member.
        EvmoneBackend(EvmoneBackend const &) = delete;
        EvmoneBackend(EvmoneBackend &&) = delete;
        EvmoneBackend &operator=(EvmoneBackend const &) = delete;
        EvmoneBackend &operator=(EvmoneBackend &&) = delete;

        Address
        deploy(Address const &from, std::span<uint8_t const> code) override;

        evmc::Result
        execute(evmc_message const &msg, evmc_revision rev) override;

        uint64_t checkpoint() override;
        void rollback(uint64_t id) override;

        byte_string get_code(Address const &) override;
        void ensure_exists(Address const &) override;

        void normalize() override;
        std::unique_ptr<SortedStateView> sorted_view() const override;

        size_t max_code_size() const override;
    };
}
