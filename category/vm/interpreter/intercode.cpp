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
        , jumpdest_map_(find_jumpdests(
              std::span<uint8_t const>{padded_code_, code.size()}))
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

    auto Intercode::find_jumpdests(std::span<uint8_t const> const code)
        -> JumpdestMap
    {
        auto jumpdests = JumpdestMap(code.size());

#ifdef MONAD_ZKVM_ZISK
        // ZisK proves a JUMPDEST bitmap directly: csrs on the syscall port with
        // the bytecode pointer, then a dummy add carrying destination and size.
        // Two instructions replace six per code byte.
        //
        // Its preconditions are the caller's to meet, and breaking one leaves
        // the program unprovable rather than unsound: both pointers 8-byte
        // aligned, the bitmap at least size/64 words, and size > 0. All three
        // are CHECKED and none assumed -- padded_code_ is aligned by the
        // padding constant and vector<uint64_t> by its allocator, and the map
        // is constructed from this same code.size() two lines above, so each
        // holds today. Any of them ceasing to hold turns a provable guest into
        // an unprovable one with nothing to point at, which is precisely the
        // failure that leaves no evidence: the machine writes whole 64-bit
        // words, so a bitmap short of size/64 is written past its end.
        auto const aligned =
            (reinterpret_cast<uintptr_t>(code.data()) % 8) == 0 &&
            (reinterpret_cast<uintptr_t>(jumpdests.words()) % 8) == 0;
        auto const covered = jumpdests.word_count() >= (code.size() + 63) / 64;
        if (aligned && covered && !code.empty()) {
            uint64_t *const dst = jumpdests.words();
            uint8_t const *const src = code.data();
            size_t const size = code.size();
            // zicsr is part of the official ZisK target architecture.
            asm volatile("csrs 0x81c, %0\n\t"
                         "add x0, %1, %2\n\t"
                         :
                         : "r"(src), "r"(dst), "r"(size)
                         : "memory");
            return jumpdests;
        }
#endif

        // Software fallback for non-ZisK builds or unmet preconditions.
        for (size_t i = 0; i < code.size(); ++i) {
            auto const op = code[i];

            if (op == EvmOpCode::JUMPDEST) {
                jumpdests.set(i);
            }

            if (is_push_opcode(op)) {
                i += get_push_opcode_index(op);
            }
        }

        return jumpdests;
    }
}
