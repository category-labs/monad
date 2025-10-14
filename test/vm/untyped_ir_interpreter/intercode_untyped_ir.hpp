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

#include <category/vm/compiler/ir/untyped.hpp>
#include <category/vm/runtime/bin.hpp>

#include <cstdint>
#include <memory>
#include <span>
#include <unordered_set>
#include <vector>

namespace monad::vm::interpreter
{
    using code_size_t = runtime::Bin<20>;

    class IntercodeUntypedIR
    {
        // 30 bytes of initial padding ensures that we can implement all
        // PUSHN opcodes by reading data from _before_ the instruction
        // pointer with a single 32-byte read, then cleaning up any
        // over-read in the result value.
        static constexpr std::size_t start_padding_size = 30;

        // 32 for a truncated PUSH32, 1 for a STOP so that we don't have to
        // worry about going off the end.
        static constexpr std::size_t end_padding_size = 32 + 1;

    public:
        using JumpdestMap = std::vector<bool>;

        explicit IntercodeUntypedIR(std::span<std::uint8_t const> const);

        IntercodeUntypedIR(std::uint8_t const *code, std::size_t code_size)
            : IntercodeUntypedIR{std::span<std::uint8_t const>{code, code_size}}
        {
        }

        ~IntercodeUntypedIR();

        std::uint8_t const *code() const noexcept
        {
            return padded_code_;
        }

        code_size_t code_size() const noexcept
        {
            return code_size_;
        }

        size_t size() const noexcept
        {
            return *code_size_;
        }

        std::span<uint8_t const> code_span() const noexcept
        {
            return {padded_code_, size_t{*code_size_}};
        }

        bool is_jumpdest(std::size_t const pc) const noexcept
        {
            return pc < *code_size_ && jumpdest_map_[pc];
        }

    private:
        std::uint8_t const *padded_code_;
        code_size_t code_size_;
        JumpdestMap jumpdest_map_;
        monad::vm::compiler::untyped::UntypedIR ir;

    public:
        std::unordered_map<std::size_t, std::vector<std::size_t>>
            fallthrough_coerce_map;
        std::unordered_map<std::size_t, std::vector<std::size_t>>
            jump_coerce_map;
        std::unordered_set<std::size_t> jumpdest_addr;

        bool valid_ir()
        {
            return std::holds_alternative<
                std::vector<monad::vm::compiler::untyped::Block>>(ir.blocks);
        }

    private:
        static std::uint8_t const *
        pad(std::span<std::uint8_t const> const code);

        static std::unordered_map<std::size_t, std::vector<std::size_t>>
        build_fallthrough_coerce_map(
            monad::vm::compiler::untyped::UntypedIR ir);

        static std::unordered_map<std::size_t, std::vector<std::size_t>>
        build_jump_coerce_map(monad::vm::compiler::untyped::UntypedIR ir);

        static std::unordered_set<std::size_t>
        build_jumpdest_addr_set(monad::vm::compiler::untyped::UntypedIR ir);

        static JumpdestMap
        find_jumpdests(std::span<std::uint8_t const> const code);
    };
}
