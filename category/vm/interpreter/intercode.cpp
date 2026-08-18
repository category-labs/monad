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

#include <category/core/monad_exception.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/interpreter/intercode.hpp>

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <span>

using namespace monad::vm::compiler;

namespace monad::vm::interpreter
{
    Intercode::Intercode(std::span<uint8_t const> const code)
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

    uint8_t const *Intercode::pad(std::span<uint8_t const> const code)
    {
        MONAD_ASSERT_THROW(
            code.size() <= *code_size_t::max(),
            "Code size exceeds maximum representable value");

        auto *buffer =
            new uint8_t[start_padding_size + code.size() + end_padding_size];

        std::fill_n(&buffer[0], start_padding_size, 0);
        std::copy(code.begin(), code.end(), &buffer[start_padding_size]);
        std::fill_n(
            &buffer[code.size() + start_padding_size], end_padding_size, 0);

        return buffer + start_padding_size;
    }

    namespace
    {
        /// Push-data length per opcode, 0 for everything else. One load replaces
        /// the two range compares and the subtract that is_push_opcode /
        /// get_push_opcode_index expand to -- and the scan below runs this test on
        /// EVERY code byte of EVERY distinct contract a block touches, which is
        /// why the function is the single hottest one in the guest.
        // The table holds the whole advance, 1 + push data, not the push
        // data alone: the +1 is otherwise an addiw inside the hot loop, on
        // every opcode of every contract.
        constexpr auto advance = [] {
            std::array<uint8_t, 256> t{};
            t.fill(1);
            for (unsigned op = PUSH0; op <= PUSH32; ++op) {
                t[op] = static_cast<uint8_t>(1 + op - PUSH0);
            }
            return t;
        }();
    }

    auto Intercode::find_jumpdests(std::span<uint8_t const> const code)
        -> JumpdestMap
    {
        auto jumpdests = JumpdestMap(code.size());


        // Raw pointer, hoisted end: the span's operator[] and the re-read of
        // code.size() per iteration are pure overhead in a loop this hot.
        uint8_t const *p = code.data();
        uint8_t const *const end = p + code.size();
        while (p < end) {
            auto const op = *p;
            if (op == EvmOpCode::JUMPDEST) {
                jumpdests.set(static_cast<size_t>(p - code.data()));
            }
            p += advance[op];
        }

        return jumpdests;
    }
}
