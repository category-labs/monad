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
        // 30 bytes of initial padding ensures that we can implement all
        // PUSHN opcodes by reading data from _before_ the instruction
        // pointer with a single 32-byte read, then cleaning up any
        // over-read in the result value.
        // 32 and not 30, which is what the read above needs: the ZisK
        // JUMPDEST precompile requires an 8-byte-aligned bytecode pointer, and
        // operator new is 16-byte aligned, so a 32-byte offset lands aligned
        // while 30 lands at 6 mod 8 every time. Two bytes per contract buys the
        // precompile; more front padding is harmless for the read.
        static constexpr size_t start_padding_size = 32;

        // 32 for a truncated PUSH32, 1 for a STOP so that we don't have to
        // worry about going off the end.
        static constexpr size_t end_padding_size = 32 + 1;

    public:
        // A bit per code byte, held in explicit 64-bit words.
        //
        // std::vector<bool> is bit-packed as well, but its layout is
        // unspecified: no guaranteed alignment, bit order within a word, or
        // absence of padding. Nothing outside the class can legitimately be
        // pointed at its storage, and its operator[] returns a proxy whose
        // codegen is the library's business rather than ours. Explicit words
        // make is_jumpdest a shift and a test, and make the buffer something a
        // precompile could be handed.
        class JumpdestMap
        {
            std::vector<uint64_t> words_;

        public:
            JumpdestMap() = default;

            explicit JumpdestMap(size_t const bits)
                : words_((bits + 63) / 64, 0)
            {
            }

            void set(size_t const i) noexcept
            {
                words_[i >> 6] |= uint64_t{1} << (i & 63);
            }

            bool test(size_t const i) const noexcept
            {
                return (words_[i >> 6] >> (i & 63)) & 1;
            }

            size_t word_count() const noexcept { return words_.size(); }

            uint64_t *words() noexcept
            {
                return words_.data();
            }
        };

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
            return pc < *code_size_ && jumpdest_map_.test(pc);
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
        uint8_t const *padded_code_;
        code_size_t code_size_;
        JumpdestMap jumpdest_map_;

        static uint8_t const *pad(std::span<uint8_t const> code);

        static JumpdestMap find_jumpdests(std::span<uint8_t const> code);
    };
}
