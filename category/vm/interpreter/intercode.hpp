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

#include <category/vm/runtime/bin.hpp>

#include <algorithm>
#include <cstdint>
#include <memory>
#include <span>
#include <vector>

namespace monad::vm::interpreter
{
    using code_size_t = runtime::Bin<20>;

    class Intercode
    {
        // PUSHN needs at least 30 leading bytes for a single 32-byte read
        // before the instruction pointer, masking out unrelated bytes.
        // Round up to 32 to preserve 8-byte alignment for guest Keccak loads.
        static constexpr size_t start_padding_size = 32;

        // 32 for a truncated PUSH32, 1 for a STOP so that we don't have to
        // worry about going off the end.
        static constexpr size_t end_padding_size = 32 + 1;

    public:
        // One bit per code byte, packed into 64-bit words.
        using JumpdestMap = std::vector<uint64_t>;

        explicit Intercode(std::span<uint8_t const> const);

        Intercode(uint8_t const *const code, size_t const code_size)
            : Intercode{std::span<uint8_t const>{code, code_size}}
        {
        }

        ~Intercode();

        uint8_t const *code() const noexcept
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

        bool is_jumpdest(size_t const pc) const noexcept
        {
            return pc < *code_size_ &&
                   ((jumpdest_map_[pc >> 6] >> (pc & 63)) & 1);
        }

        [[gnu::always_inline]]
        size_t copy_code(
            size_t const offset, uint8_t *const buffer,
            size_t const buffer_size) const
        {
            auto const code_size = size();
            if (offset > code_size) {
                return 0;
            }
            auto const n = std::min(code_size - offset, buffer_size);
            std::copy_n(code() + offset, n, buffer);
            return n;
        }

    private:
        uint8_t *padded_code_;
        code_size_t code_size_;
        JumpdestMap jumpdest_map_;

        // Allocates the code buffer with its padding zeroed and the code bytes
        // uninitialized; returns a pointer to the first code byte.
        static uint8_t *allocate_padded(size_t code_size);

        // `padded` must come from allocate_padded: the scan reads its zero
        // padding past the end of the code.
        static JumpdestMap
        copy_and_find_jumpdests(std::span<uint8_t const> code, uint8_t *padded);
    };
}
