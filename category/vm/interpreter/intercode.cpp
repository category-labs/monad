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
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/interpreter/jumpdest_scan.hpp>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <span>

namespace monad::vm::interpreter
{
    Intercode::Intercode(std::span<uint8_t const> const code)
        : padded_code_(allocate_padded(code.size()))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        , jumpdest_map_(copy_and_find_jumpdests(code, padded_code_))
    {
    }

    Intercode::~Intercode()
    {
        delete[] (padded_code_ - start_padding_size);
    }

    uint8_t *Intercode::allocate_padded(size_t const code_size)
    {
        MONAD_ASSERT_THROW(
            code_size <= *code_size_t::max(),
            "Code size exceeds maximum representable value");

        auto *buffer =
            new uint8_t[start_padding_size + code_size + end_padding_size];

        std::fill_n(&buffer[0], start_padding_size, 0);
        std::fill_n(
            &buffer[code_size + start_padding_size], end_padding_size, 0);

        return buffer + start_padding_size;
    }

    auto Intercode::copy_and_find_jumpdests(
        std::span<uint8_t const> const code, uint8_t *const padded)
        -> JumpdestMap
    {
        static_assert(end_padding_size >= detail::avx2_scan_padding);
        auto jumpdests =
            JumpdestMap(detail::jumpdest_word_count(code.size()), 0);
#if defined(__AVX2__)
        detail::copy_and_find_jumpdests_avx2(
            code.data(), padded, code.size(), jumpdests.data());
#else
        std::copy(code.begin(), code.end(), padded);
        detail::find_jumpdests_scalar(padded, code.size(), jumpdests.data());
#endif
        return jumpdests;
    }
}
