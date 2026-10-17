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
#include <cstring>
#include <span>

using namespace monad::vm::compiler;

namespace monad::vm::interpreter
{
    Intercode::Intercode(std::span<uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        // A truncated PUSH may advance past the code, but stays in the padding.
        , jumpdest_map_(find_jumpdests(code_span()))
    {
    }

#if defined(MONAD_ZKVM_AIRBENDER)
    namespace
    {
        uint32_t in_place_size(size_t const code_size)
        {
            MONAD_ASSERT(code_size <= *code_size_t::max());
            return static_cast<uint32_t>(code_size);
        }
    }

    Intercode::Intercode(
        uint8_t const *const padded_code, size_t const code_size, in_place_t)
        : padded_code_(padded_code)
        , code_size_(code_size_t::unsafe_from(in_place_size(code_size)))
        , jumpdest_map_(find_jumpdests(code_span()))
    {
    }
#endif

#ifdef MONAD_ZKVM_ZISK
    Intercode::Intercode(
        uint8_t const *const padded_code, size_t const code_size,
        uint64_t const *const jumpdest_words)
        : padded_code_(padded_code)
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code_size)))
        , jumpdest_map_(code_size)
    {
        std::memcpy(
            jumpdest_map_.words(),
            jumpdest_words,
            (code_size + 63) / 64 * sizeof(uint64_t));
    }
#endif

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
        // Whole advance per opcode: 1 + immediate data, 1 for non-PUSH.
        // One lookup replaces range checks and subtraction during the scan,
        // and holding the +1 here keeps an addiw out of the hot loop, which
        // runs on every code byte of every distinct contract.
        constexpr auto advance = [] {
            std::array<uint8_t, 256> t{};
            t.fill(1);
            for (unsigned op = PUSH0; op <= PUSH32; ++op) {
                t[op] = static_cast<uint8_t>(1 + op - PUSH0);
            }
            return t;
        }();
    }

#ifdef MONAD_ZKVM_ZISK
}

// The JUMPDEST map of a code the guest knows in advance, whose words a known
// code's analysis copies instead of running; null for any other code. The
// guest's table defines it; this default knows none.
extern "C" [[gnu::weak]] uint64_t const *
monad_zkvm_known_jumpdests(uint8_t const *, size_t) noexcept
{
    return nullptr;
}

namespace monad::vm::interpreter
{
#endif
    auto Intercode::find_jumpdests(std::span<uint8_t const> const code)
        -> JumpdestMap
    {
        static_assert(end_padding_size >= PUSH32 - PUSH0);
        auto jumpdests = JumpdestMap(code.size());

#ifdef MONAD_ZKVM_ZISK
        // ZisK's JUMPDEST precompile takes src via csrs, then dst and size via
        // the following add. It requires nonempty input, 8-byte-aligned
        // pointers and enough space for whole 64-bit output words.
        auto const aligned =
            (reinterpret_cast<uintptr_t>(code.data()) % 8) == 0 &&
            (reinterpret_cast<uintptr_t>(jumpdests.words()) % 8) == 0;
        auto const covered = jumpdests.word_count() >= (code.size() + 63) / 64;
        if (aligned && covered && !code.empty()) {
            uint64_t *const dst = jumpdests.words();
            uint8_t const *const src = code.data();
            size_t const size = code.size();
            if (uint64_t const *const known =
                    monad_zkvm_known_jumpdests(src, size)) {
                std::memcpy(dst, known, (size + 63) / 64 * sizeof(uint64_t));
                return jumpdests;
            }
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
        // Skip PUSH data: its bytes cannot be jump destinations.
        uint8_t const *p = code.data();
        uint8_t const *const end = p + code.size();
#if defined(MONAD_ZKVM_AIRBENDER)
        // Two opcodes a turn and one end test, which every opcode of every
        // code the block runs otherwise pays. The second needs none of its
        // own: from below the end an opcode advances at most 33 bytes, into
        // the end padding, whose zero bytes are STOPs -- no JUMPDEST, and the
        // next turn's test ends the scan.
        static_assert(end_padding_size >= PUSH32 - PUSH0 + 1);
        while (p < end) {
            auto op = *p;
            if (op == EvmOpCode::JUMPDEST) {
                jumpdests.set(static_cast<size_t>(p - code.data()));
            }
            p += advance[op];
            op = *p;
            if (op == EvmOpCode::JUMPDEST) {
                jumpdests.set(static_cast<size_t>(p - code.data()));
            }
            p += advance[op];
        }
#else
        while (p < end) {
            auto const op = *p;
            if (op == EvmOpCode::JUMPDEST) {
                jumpdests.set(static_cast<size_t>(p - code.data()));
            }
            p += advance[op];
        }
#endif

        return jumpdests;
    }
}
