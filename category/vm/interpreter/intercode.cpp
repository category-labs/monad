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

#include <category/vm/core/assert.h>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>

#include <algorithm>
#include <cstdint>
#include <span>

using namespace monad::vm::compiler;

namespace monad::vm::interpreter
{
    Intercode::Intercode(std::span<std::uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        , jumpdest_map_(find_jumpdests(code))
    {
    }

    Intercode::~Intercode()
    {
        delete[] (padded_code_ - start_padding_size);
    }

    std::uint8_t const *Intercode::pad(std::span<std::uint8_t const> const code)
    {
        MONAD_VM_ASSERT(code.size() <= *code_size_t::max());
        auto *buffer = new std::uint8_t
            [start_padding_size + code.size() + end_padding_size];

        std::fill_n(&buffer[0], start_padding_size, 0);
        std::copy(code.begin(), code.end(), &buffer[start_padding_size]);
        std::fill_n(
            &buffer[code.size() + start_padding_size], end_padding_size, 0);

        return buffer + start_padding_size;
    }

    auto Intercode::find_jumpdests(std::span<std::uint8_t const> const code)
        -> JumpdestMap
    {
        auto jumpdests = JumpdestMap(code.size(), false);

        for (auto i = 0u; i < code.size(); ++i) {
            auto const op = code[i];

            if (op == EvmOpCode::JUMPDEST) {
                jumpdests[i] = true;
            }

            if (is_push_opcode(op)) {
                i += get_push_opcode_index(op);
            }
        }

        return jumpdests;
    }
}
