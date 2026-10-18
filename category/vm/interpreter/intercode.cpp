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
#if defined(MONAD_ZKVM_AIRBENDER)
    namespace
    {
        uint32_t in_place_size(size_t const code_size)
        {
            MONAD_ASSERT(code_size <= *code_size_t::max());
            return static_cast<uint32_t>(code_size);
        }

        // A byte per chunk, from the bump allocator: fresh memory, which
        // reads zero on Airbender (vm/memory_pool.cpp), so no chunk is
        // analysed yet. Nothing frees it, which this guest never does.
        uint8_t *new_chunk_ends(size_t const code_size)
        {
            return static_cast<uint8_t *>(::operator new(
                (code_size >> Intercode::lazy_chunk_shift) + 1));
        }
    }

    // The map is analysed by chunks, as jumps need them (analyse_chunk).
    Intercode::Intercode(std::span<uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        , jumpdest_map_(code.size())
        , chunk_ends_(new_chunk_ends(code.size()))
    {
    }

    Intercode::Intercode(
        uint8_t const *const padded_code, size_t const code_size, in_place_t)
        : padded_code_(padded_code)
        , code_size_(code_size_t::unsafe_from(in_place_size(code_size)))
        , jumpdest_map_(code_size)
        , chunk_ends_(new_chunk_ends(code_size))
    {
    }
#else
    Intercode::Intercode(std::span<uint8_t const> const code)
        : padded_code_(pad(code))
        , code_size_(
              code_size_t::unsafe_from(static_cast<uint32_t>(code.size())))
        // A truncated PUSH may advance past the code, but stays in the padding.
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

#if defined(MONAD_ZKVM_AIRBENDER)
    namespace
    {
        // How far below a chunk's start the search for an instruction
        // boundary goes before the chunks below are analysed in order.
        constexpr size_t lazy_back_limit = size_t{1}
                                           << Intercode::lazy_chunk_shift;
    }

    // Chunk k's JUMPDESTs, scanned from an instruction boundary at or below
    // its start: where the scan of chunk k - 1 stopped, if it ran; else the
    // highest position b at or below the start that no byte of the 32 before
    // it can cover as a PUSH's data -- for each q in [b - 32, b), q + its
    // PUSH size (0 for any other opcode) < b. Such a b is a boundary: the
    // last boundary below it, q0, starts an instruction whose data ends
    // before b, so the next boundary, q0 + advance[code[q0]], is at most b,
    // and being the next after the last below b, it is b. Positions of 45 %
    // of real code pass; from a chunk's start the search goes back one byte
    // at the median, 28 at the 90th percentile. Past lazy_back_limit it
    // stops, and the chunks below are analysed in order from the highest
    // analysed one (or the code's start), so a code whose bytes all look
    // like PUSH32s costs its whole length once, not once per chunk.
    void Intercode::analyse_chunk(size_t const k) noexcept
    {
        uint8_t const *const code = padded_code_;
        size_t const start = k << lazy_chunk_shift;
        // By pointers, as find_jumpdests: an index costs an add a byte.
        uint8_t const *p;
        if (k == 0) {
            p = code;
        }
        else if (chunk_ends_[k - 1] != 0) {
            p = code + start + chunk_ends_[k - 1] - 1;
        }
        else {
            // Bounds clamped to the code's start, so no pointer leaves it.
            auto const below = [code](uint8_t const *const x, size_t const n) {
                return static_cast<size_t>(x - code) > n ? x - n : code;
            };
            uint8_t const *b = code + start;
            uint8_t const *stop = below(b, 32);
            uint8_t const *const low = below(b, lazy_back_limit);
            uint8_t const *q = b;
            // The bytes from b - 1 down to b - 32 (or the code's start),
            // each a PUSH that would cover b or not; one that would makes
            // its own position the candidate, with the 32 bytes below it.
            while (q > stop) {
                --q;
                if (MONAD_UNLIKELY(q + advance[*q] > b)) {
                    b = q;
                    stop = below(b, 32);
                    if (MONAD_UNLIKELY(b < low)) {
                        break;
                    }
                }
            }
            if (MONAD_UNLIKELY(b < low)) {
                size_t j = k - 1;
                while (j != 0 && chunk_ends_[j - 1] == 0) {
                    --j;
                }
                for (; j < k; ++j) {
                    analyse_chunk(j);
                }
                p = code + start + chunk_ends_[k - 1] - 1;
            }
            else {
                p = b;
            }
        }
        // As find_jumpdests scans, two opcodes a turn. The second may pass
        // the chunk's end: then it is the next chunk's first, a boundary the
        // scan reached, and its bit is as exact; at the code's end it is in
        // the zero padding. The scan stops at most 2 * 33 bytes past the end.
        uint8_t const *const end =
            code + std::min(size(), start + (size_t{1} << lazy_chunk_shift));
        while (p < end) {
            auto op = *p;
            if (op == EvmOpCode::JUMPDEST) {
                jumpdest_map_.set(static_cast<size_t>(p - code));
            }
            p += advance[op];
            op = *p;
            if (op == EvmOpCode::JUMPDEST) {
                jumpdest_map_.set(static_cast<size_t>(p - code));
            }
            p += advance[op];
        }
        chunk_ends_[k] = static_cast<uint8_t>(p - end + 1);
    }

    bool Intercode::lazy_is_jumpdest(size_t const pc) noexcept
    {
        if (pc >= size()) {
            return false;
        }
        size_t const k = pc >> lazy_chunk_shift;
        if (chunk_ends_[k] == 0) {
            analyse_chunk(k);
        }
        return jumpdest_map_.test(pc);
    }
#endif
}

#if defined(MONAD_ZKVM_AIRBENDER)
// Intercode::lazy_test's callee: the analysis in t1, the position in t2, the
// answer back in t1, the return address in t0. Every other register the
// handler may hold is saved around the C++ call.
extern "C" uintptr_t
monad_vm_lazy_jumpdest(uintptr_t const analysis, size_t const pc) noexcept
{
    auto *const ic = reinterpret_cast<monad::vm::interpreter::Intercode *>(
        analysis);
    return ic->lazy_is_jumpdest(pc) ? 1 : 0;
}

asm(R"(
    .section .text.monad_vm_lazy_jumpdest_trampoline,"ax",@progbits
    .globl monad_vm_lazy_jumpdest_trampoline
    .p2align 2
monad_vm_lazy_jumpdest_trampoline:
    addi sp, sp, -64
    sw ra, 0(sp)
    sw t0, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    sw a0, 28(sp)
    sw a1, 32(sp)
    sw a2, 36(sp)
    sw a3, 40(sp)
    sw a4, 44(sp)
    sw a5, 48(sp)
    sw a6, 52(sp)
    sw a7, 56(sp)
    mv a0, t1
    mv a1, t2
    call monad_vm_lazy_jumpdest
    mv t1, a0
    lw ra, 0(sp)
    lw t0, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    lw a0, 28(sp)
    lw a1, 32(sp)
    lw a2, 36(sp)
    lw a3, 40(sp)
    lw a4, 44(sp)
    lw a5, 48(sp)
    lw a6, 52(sp)
    lw a7, 56(sp)
    addi sp, sp, 64
    jr t0
    .previous
)");
#endif
