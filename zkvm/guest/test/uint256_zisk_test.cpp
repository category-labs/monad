// Copyright (C) 2025-26 Category Labs, Inc.
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

// Compare software guest overrides against intx in host and guest modes.

#include <category/core/runtime/uint256.hpp>
#include <category/core/runtime/uint256/overrides.hpp>

#include <intx/intx.hpp>

#ifdef MONAD_ZKVM_UINT256_SELFTEST
    #include <io-interface/zkvm_io.h>
    #include <zkvm/core/zkvm_halt.h>
#endif

#include <array>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

#if !defined(MONAD_ZKVM_ZISK)
    #error "This test checks the ZisK branches; define MONAD_ZKVM_ZISK."
#endif

// Ensure the include path selects the guest override header.
static_assert(monad::uint256::overrides::enabled);

namespace
{
    using monad::uint256_t;

    ::intx::uint256 to_intx(uint256_t const &x)
    {
        return ::intx::uint256{x[0], x[1], x[2], x[3]};
    }

#ifndef MONAD_ZKVM_UINT256_SELFTEST
    void print(char const *const name, uint256_t const &x)
    {
        std::fprintf(
            stderr,
            " %s=0x%016" PRIx64 "%016" PRIx64 "%016" PRIx64 "%016" PRIx64,
            name,
            x[3],
            x[2],
            x[1],
            x[0]);
    }

#endif

    void require(
        bool const ok, char const *const operation, uint256_t const &x,
        uint256_t const &y)
    {
        if (!ok) {
#ifdef MONAD_ZKVM_UINT256_SELFTEST
            zkvm_halt(1);
#else
            std::fprintf(stderr, "uint256 on ZisK: wrong %s:", operation);
            print("x", x);
            print("y", y);
            std::fputc('\n', stderr);
            std::exit(1);
#endif
        }
    }

    // SplitMix64, so that a failure reproduces.
    uint64_t next_random(uint64_t &state)
    {
        state += 0x9e3779b97f4a7c15;
        uint64_t z = state;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9;
        z = (z ^ (z >> 27)) * 0x94d049bb133111eb;
        return z ^ (z >> 31);
    }

    // Words at the signed and unsigned boundaries, placed so that many pairs
    // share their upper words, then random values, half of them one word.
    std::vector<uint256_t> make_inputs()
    {
        constexpr std::array<uint64_t, 8> words{
            0,
            1,
            0x7fffffffffffffff,
            0x8000000000000000,
            0xffffffffffffffff,
            0x0123456789abcdef,
            0xfedcba9876543210,
            0xaaaaaaaaaaaaaaaa};
        std::vector<uint256_t> inputs;
        for (uint64_t const a : words) {
            for (uint64_t const b : words) {
                inputs.emplace_back(a, 0, 0, b);
                inputs.emplace_back(b, a, a, b);
                inputs.emplace_back(a, b, a ^ b, a);
            }
        }
        uint64_t state = 0;
        for (int i = 0; i < 64; ++i) {
            uint64_t const w0 = next_random(state);
            uint64_t const w1 = next_random(state);
            uint64_t const w2 = next_random(state);
            uint64_t const w3 = next_random(state);
            inputs.emplace_back(w0, w1, w2, w3);
            inputs.emplace_back(next_random(state));
        }
        return inputs;
    }

    void check_comparisons(std::vector<uint256_t> const &inputs)
    {
        for (auto const &x : inputs) {
            auto const reference_x = to_intx(x);
            require(static_cast<bool>(x) == (reference_x != 0), "bool", x, x);
            for (auto const &y : inputs) {
                auto const reference_y = to_intx(y);
                require((x == y) == (reference_x == reference_y), "==", x, y);
                require((x != y) == (reference_x != reference_y), "!=", x, y);
                require((x < y) == (reference_x < reference_y), "<", x, y);
                require((x <= y) == (reference_x <= reference_y), "<=", x, y);
                require((x > y) == (reference_x > reference_y), ">", x, y);
                require((x >= y) == (reference_x >= reference_y), ">=", x, y);
                require(
                    slt(x, y) == ::intx::slt(reference_x, reference_y),
                    "slt",
                    x,
                    y);
            }
        }
    }

    // Compare products through intx, independently of uint256_t's ==.
    void check_multiply(std::vector<uint256_t> const &inputs)
    {
        for (auto const &x : inputs) {
            for (auto const &y : inputs) {
                require(to_intx(x * y) == to_intx(x) * to_intx(y), "*", x, y);
            }
        }
    }

    // Every shift up to past 256, then amounts with upper words set.
    std::vector<uint256_t> make_shifts()
    {
        std::vector<uint256_t> shifts;
        for (uint64_t shift = 0; shift <= 260; ++shift) {
            shifts.emplace_back(shift);
        }
        shifts.emplace_back(0, 1, 0, 0);
        shifts.emplace_back(64, 0, 0, 1);
        uint64_t const ones = ~uint64_t{0};
        shifts.emplace_back(ones, ones, ones, ones);
        return shifts;
    }

    // Arithmetic right shift: complement a negative value, shift it
    // logically, then complement the result.
    ::intx::uint256
    sar_reference(::intx::uint256 const &x, ::intx::uint256 const &shift)
    {
        bool const negative = (x[3] >> 63) != 0;
        return negative ? ~(~x >> shift) : x >> shift;
    }

    void check_shifts(std::vector<uint256_t> const &inputs)
    {
        auto const shifts = make_shifts();
        for (auto const &x : inputs) {
            auto const reference_value = to_intx(x);
            for (auto const &shift : shifts) {
                auto const reference_shift = to_intx(shift);
                require(
                    to_intx(x << shift) == (reference_value << reference_shift),
                    "<<",
                    x,
                    shift);
                require(
                    to_intx(x >> shift) == (reference_value >> reference_shift),
                    ">>",
                    x,
                    shift);
                require(
                    to_intx(sar(shift, x)) ==
                        sar_reference(reference_value, reference_shift),
                    "sar",
                    x,
                    shift);
                if (shift[1] == 0 && shift[2] == 0 && shift[3] == 0) {
                    require(
                        to_intx(x << shift[0]) ==
                            (reference_value << reference_shift),
                        "<< by a word",
                        x,
                        shift);
                }
            }
        }
    }
}

void check_software()
{
    auto const inputs = make_inputs();
    check_comparisons(inputs);
    check_multiply(inputs);
    check_shifts(inputs);
}

#ifdef MONAD_ZKVM_UINT256_SELFTEST
// The Rust launcher calls the same entry symbol in both build modes.
extern "C" void monad_zkvm_execute_witness()
{
    uint8_t const *input = nullptr;
    size_t size = 0;
    read_input(&input, &size);
    auto const test = size == 1 ? input[0] : uint8_t{255};
    uint32_t failures = 1;
    if (test == 0) {
        check_software();
        failures = 0;
    }
    // A rejected hint must halt before reaching the completion marker.
    unsigned char output[32]{0, 0, 0, 0, 'U', '2', '5', '6', test};
    __builtin_memcpy(output, &failures, sizeof(failures));
    write_output(output, sizeof(output));
}
#else
int main()
{
    check_software();
    return 0;
}
#endif
