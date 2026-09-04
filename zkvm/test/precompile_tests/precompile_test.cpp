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

// Precompile golden-vector test guest.
//
// Reads a serialized blob of go-ethereum precompile vectors (produced by
// zkvm/test/gen_precompile_vectors.py) via the eth-act read_input ABI, runs
// each vector through the matching precompile `_execute` shim, and checks the
// result. On SP1/ZisK those shims route crypto through the zkvm_* accelerators,
// so this exercises the accelerator ABI directly — no block witness needed.
//
// The witness guest (ffi.cpp) and this test guest expose different entry
// symbols; each backend links a thin main that calls one of them.
//
// Blob layout (LE): "PT01" | count u32 | per case:
//   addr u16 | input_len u32 | input | kind u8 | out_len u32 | out
//   kind 0 = success (out = expected output), 1 = failure (precompile rejects).
// Output (LE): "PR01" | total u32 | passed u32 | failed u32 | logged u32 |
//   logged * { index u32 | addr u16 | got_status u8 } (capped, ZisK-safe).

#include <zkvm/core/zkvm_io.h>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <cstddef>
#include <cstdint>
#include <cstring>

namespace
{
    using namespace monad;

    // The revision used to instantiate the two gas functions that gate
    // malformed input (expmod, blake2f); OSAKA activates every precompile. The
    // gas guard mirrors check_call_eth_precompile: a nullopt cost means the
    // input is invalid, so we report failure without calling `_execute` (which
    // may assert on it).
    using GuardTraits = EvmTraits<MONAD_ETH_OSAKA>;

    PrecompileResult
    run_one(std::uint16_t const addr, byte_string_view const input)
    {
        switch (addr) {
        case 0x01:
            return ecrecover_execute(input);
        case 0x02:
            return sha256_execute(input);
        case 0x03:
            return ripemd160_execute(input);
        case 0x04:
            return identity_execute(input);
        case 0x05:
            if (!expmod_gas_cost<GuardTraits>(input).has_value()) {
                return PrecompileResult::failure();
            }
            return expmod_execute(input);
        case 0x06:
            return ecadd_execute(input);
        case 0x07:
            return ecmul_execute(input);
        case 0x08:
            return snarkv_execute(input);
        case 0x09:
            if (!blake2bf_gas_cost<GuardTraits>(input).has_value()) {
                return PrecompileResult::failure();
            }
            return blake2bf_execute(input);
        case 0x0a:
            return point_evaluation_execute(input);
        case 0x0b:
            return bls12_g1_add_execute(input);
        case 0x0c:
            return bls12_g1_msm_execute(input);
        case 0x0d:
            return bls12_g2_add_execute(input);
        case 0x0e:
            return bls12_g2_msm_execute(input);
        case 0x0f:
            return bls12_pairing_check_execute(input);
        case 0x10:
            return bls12_map_fp_to_g1_execute(input);
        case 0x11:
            return bls12_map_fp2_to_g2_execute(input);
        case 0x0100:
            return p256_verify_execute(input);
        default:
            return PrecompileResult::failure();
        }
    }

    // Capped so the failure log fits ZisK's 256-byte committed-output limit
    // (16-byte header + 32 * 7-byte records = 240 bytes).
    constexpr std::uint32_t MAX_LOGGED = 32;

    std::uint32_t rd_u32(std::uint8_t const *const p)
    {
        std::uint32_t v;
        std::memcpy(&v, p, 4);
        return v;
    }

    std::uint16_t rd_u16(std::uint8_t const *const p)
    {
        std::uint16_t v;
        std::memcpy(&v, p, 2);
        return v;
    }

} // namespace

extern "C" void monad_zkvm_run_precompile_tests(void)
{
    std::uint8_t const *input = nullptr;
    std::size_t input_len = 0;
    read_input(&input, &input_len);

    MONAD_ASSERT(input_len >= 8);
    MONAD_ASSERT(std::memcmp(input, "PT01", 4) == 0);
    std::uint32_t const count = rd_u32(input + 4);

    std::uint8_t const *p = input + 8;
    std::uint8_t const *const end = input + input_len;

    std::uint32_t total = 0;
    std::uint32_t passed = 0;
    std::uint32_t failed = 0;
    std::uint32_t logged = 0;
    std::uint8_t log[MAX_LOGGED * 7];

    for (std::uint32_t i = 0; i < count; ++i) {
        MONAD_ASSERT(p + 6 <= end);
        std::uint16_t const addr = rd_u16(p);
        std::uint32_t const in_len = rd_u32(p + 2);
        p += 6;
        MONAD_ASSERT(p + in_len <= end);
        monad::byte_string_view const in{p, in_len};
        p += in_len;

        MONAD_ASSERT(p + 5 <= end);
        std::uint8_t const kind = p[0];
        std::uint32_t const out_len = rd_u32(p + 1);
        p += 5;
        MONAD_ASSERT(p + out_len <= end);
        std::uint8_t const *const expected = p;
        p += out_len;

        auto const r = run_one(addr, in);
        bool ok;
        if (kind == 0) {
            ok = r.status_code == EVMC_SUCCESS && r.output_size == out_len &&
                 (out_len == 0 || std::memcmp(r.obuf, expected, out_len) == 0);
        }
        else {
            ok = r.status_code != EVMC_SUCCESS;
        }

        ++total;
        if (ok) {
            ++passed;
        }
        else {
            ++failed;
            if (logged < MAX_LOGGED) {
                std::uint8_t *const e = log + logged * 7;
                std::memcpy(e, &i, 4);
                std::memcpy(e + 4, &addr, 2);
                e[6] = static_cast<std::uint8_t>(r.status_code);
                ++logged;
            }
        }
    }

    std::uint8_t hdr[16];
    static constexpr std::uint8_t MAGIC[4]{'P', 'R', '0', '1'};
    std::memcpy(hdr, MAGIC, 4);
    std::memcpy(hdr + 4, &total, 4);
    std::memcpy(hdr + 8, &passed, 4);
    std::memcpy(hdr + 12, &failed, 4);
    write_output(hdr, sizeof(hdr));
    std::uint8_t lc[4];
    std::memcpy(lc, &logged, 4);
    write_output(lc, sizeof(lc));
    write_output(log, logged * 7);
}
