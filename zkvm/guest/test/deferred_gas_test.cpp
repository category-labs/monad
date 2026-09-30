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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/host.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/runtime/types.hpp>

#include <array>
#include <cstdint>
#include <initializer_list>
#include <span>
#include <vector>

namespace
{
    using namespace monad;
    using namespace monad::vm;
    using enum compiler::EvmOpCode;
    using GasTraits = EvmTraits<MONAD_ETH_CANCUN>;

    // Any callback other than get_tx_context is observable by the witness
    // provider. Count reads as well as writes: a reverted read can still fail
    // when the corresponding proof is absent.
    struct CountingHost final : vm::Host
    {
        mutable unsigned accesses = 0;
        evmc_tx_context tx{};

        CountingHost()
        {
            tx.block_number = 1;
        }

        bool account_exists(evmc::address const &) const noexcept override
        {
            ++accesses;
            return false;
        }

        evmc::bytes32 get_storage(evmc::address const &, evmc::bytes32 const &)
            const noexcept override
        {
            ++accesses;
            return {};
        }

        void get_storage_into(
            evmc::address const &, evmc::bytes32 const &,
            evmc_bytes32 &out) const noexcept override
        {
            ++accesses;
            out = {};
        }

        evmc_access_status sload_into(
            evmc::address const &, evmc::bytes32 const &, bool,
            evmc_bytes32 &out) noexcept override
        {
            ++accesses;
            out = {};
            return EVMC_ACCESS_WARM;
        }

        std::optional<Address>
        delegate_of(evmc::address const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        evmc_storage_status set_storage(
            evmc::address const &, evmc::bytes32 const &,
            evmc::bytes32 const &) noexcept override
        {
            ++accesses;
            return EVMC_STORAGE_ASSIGNED;
        }

        evmc::uint256be
        get_balance(evmc::address const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        size_t get_code_size(evmc::address const &) const noexcept override
        {
            ++accesses;
            return 0;
        }

        evmc::bytes32
        get_code_hash(evmc::address const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        size_t copy_code(
            evmc::address const &, size_t, uint8_t *, size_t) const override
        {
            ++accesses;
            return 0;
        }

        bool selfdestruct(
            evmc::address const &, evmc::address const &) noexcept override
        {
            ++accesses;
            return false;
        }

        evmc::Result call(evmc_message const &) noexcept override
        {
            ++accesses;
            return evmc::Result{EVMC_FAILURE, 0, 0};
        }

        evmc_tx_context const *get_tx_context() const noexcept override
        {
            return &tx;
        }

        evmc::bytes32 get_block_hash(int64_t) const noexcept override
        {
            ++accesses;
            return {};
        }

        void emit_log(
            evmc::address const &, uint8_t const *, size_t,
            evmc::bytes32 const *, size_t) noexcept override
        {
            ++accesses;
        }

        evmc_access_status access_account(evmc::address const &) override
        {
            ++accesses;
            return EVMC_ACCESS_WARM;
        }

        evmc_access_status access_storage(
            evmc::address const &, evmc::bytes32 const &) noexcept override
        {
            ++accesses;
            return EVMC_ACCESS_WARM;
        }

        evmc::bytes32 get_transient_storage(
            evmc::address const &,
            evmc::bytes32 const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        void set_transient_storage(
            evmc::address const &, evmc::bytes32 const &,
            evmc::bytes32 const &) noexcept override
        {
            ++accesses;
        }

        evmc_page_storage_status update_page(
            evmc::address const &, evmc::bytes32 const &,
            evmc_storage_status) noexcept override
        {
            ++accesses;
            return {};
        }
    };

    struct Outcome
    {
        evmc_status_code status;
        int64_t gas;
        int64_t refund;
        size_t output;
        unsigned accesses;
    };

    Outcome run(std::span<uint8_t const> code, int64_t gas)
    {
        CountingHost host;
        evmc_message msg{};
        msg.gas = gas;
        auto ctx = runtime::Context::from(
            &CountingHost::get_interface(), host.to_context(), &msg, code);
        interpreter::Intercode analysis{code};
        std::array<uint256_t, 1024> stack;
        interpreter::execute<GasTraits>(ctx, analysis, stack.data());
        auto result = ctx.copy_to_evmc_result<GasTraits>();
        return {
            result.status_code,
            result.gas_left,
            result.gas_refund,
            result.output_size,
            host.accesses};
    }

    bool failed_cleanly(Outcome const &r)
    {
        // A stack error can precede the delayed OOG. Both exceptional statuses
        // must consume all gas, return no data and perform no host access.
        return r.status != EVMC_SUCCESS && r.status != EVMC_REVERT &&
               r.gas == 0 && r.refund == 0 && r.output == 0 && r.accesses == 0;
    }
}

extern "C" uint32_t monad_zkvm_deferred_gas_test()
{
    uint32_t failures = 0;
    unsigned test = 0;
    auto check = [&](bool ok) {
        if (!ok) {
            failures |= uint32_t{1} << test;
        }
        ++test;
    };
    auto exhausted = [&](std::initializer_list<uint8_t> code, int64_t gas) {
        check(failed_cleanly(run(std::span{code.begin(), code.size()}, gas)));
    };

    // Ordinary and padded STOP; no successful exit with deferred negative gas.
    exhausted({PUSH1, 0x00, 0x00}, 2);
    exhausted({PUSH1, 0x00}, 2);
    exhausted({PUSH1}, 2); // Truncated immediate reads zero padding.
    exhausted({PUSH1, 0, PUSH1, 0, RETURN}, 5); // RETURN empty output.
    exhausted(
        {PUSH1, 0, PUSH1, 0, REVERT}, 5); // REVERT must become exceptional.
    exhausted({PUSH1, 0, GAS, 0x00}, 2); // GAS.
    exhausted({JUMPDEST, PUSH1, 0, JUMP}, 3); // Backward JUMP must terminate.
    exhausted({PUSH1, 0, PUSH1, 0, JUMPI}, 5); // Untaken JUMPI still checks.
    exhausted({PUSH1, 0, 0xfe}, 2); // INVALID after deferred OOG.
    exhausted({PUSH1, 0, ADD}, 2); // Stack underflow after deferred OOG.
    exhausted({PUSH1, 0, MLOAD}, 2); // MLOAD: no allocation after OOG.
    exhausted({PUSH1, 0, PUSH1, 0, SSTORE}, 5); // SSTORE.
    exhausted({PUSH1, 0, PUSH1, 0, TSTORE}, 5); // TSTORE.
    exhausted({PUSH1, 0, SELFDESTRUCT}, 2); // SELFDESTRUCT.
    exhausted({PUSH1, 0, PUSH1, 0, LOG0}, 5); // LOG0.
    exhausted({PUSH1, 0, SLOAD}, 2); // SLOAD.
    exhausted({PUSH1, 0, BLOCKHASH}, 2); // BLOCKHASH(0) is in range.
    exhausted({PUSH1, 0, SELFBALANCE}, 2); // SELFBALANCE.
    exhausted({PUSH1, 0, TLOAD}, 2); // TLOAD.
    // Also fail in the host-reading opcode itself, not only its predecessor.
    exhausted({PUSH1, 0, BLOCKHASH}, 22);
    exhausted({SELFBALANCE}, 4);
    exhausted({PUSH1, 0, TLOAD}, 102);

    std::vector<uint8_t> overflow(1025, PUSH0); // PUSH0, stack capacity 1024.
    check(failed_cleanly(run(overflow, 2047)));
    std::vector<uint8_t> call(7, PUSH0);
    call.push_back(CALL);
    check(failed_cleanly(run(call, 13))); // CALL must not reach the host.

    // Sweep the exact success boundary of a pure chain (3 + 3 + 3 + 2).
    std::array<uint8_t, 7> const pure{PUSH1, 1, PUSH1, 2, ADD, POP, 0x00};
    bool boundary = true;
    for (int64_t gas = 0; gas <= 13; ++gas) {
        auto const r = run(pure, gas);
        boundary &= gas < 11
                        ? failed_cleanly(r)
                        : r.status == EVMC_SUCCESS && r.gas == gas - 11 &&
                              r.output == 0 && r.refund == 0 && r.accesses == 0;
    }
    check(boundary);
    // At exactly the required gas, RETURN and REVERT retain their status.
    std::array<uint8_t, 5> const ret{PUSH1, 0, PUSH1, 0, RETURN};
    std::array<uint8_t, 5> const rev{PUSH1, 0, PUSH1, 0, REVERT};
    auto const r = run(ret, 6);
    auto const v = run(rev, 6);
    check(r.status == EVMC_SUCCESS && r.gas == 0 && r.output == 0);
    check(v.status == EVMC_REVERT && v.gas == 0 && v.output == 0);
    // The extra host-read checkpoints must not reject affordable reads.
    bool reads = true;
    for (auto const [op, cost] : std::array<std::pair<uint8_t, int64_t>, 3>{
             {{BLOCKHASH, 23}, {SELFBALANCE, 8}, {TLOAD, 103}}}) {
        std::array<uint8_t, 4> const code{PUSH1, 0, op, STOP};
        auto const result = run(code, cost);
        reads &= result.status == EVMC_SUCCESS && result.gas == 0 &&
                 result.accesses == 1;
    }
    check(reads);

    bool effects = true;
    for (auto const [op, operands] :
         std::array<std::pair<uint8_t, unsigned>, 8>{
             {{MSTORE, 2},
              {MSTORE8, 2},
              {SHA3, 2},
              {CREATE, 3},
              {CREATE2, 4},
              {CALLCODE, 7},
              {DELEGATECALL, 6},
              {STATICCALL, 6}}}) {
        std::vector<uint8_t> code(operands, PUSH0);
        code.push_back(op);
        effects &= failed_cleanly(run(code, 2 * operands - 1));
    }
    // The allocation suffix stores 0x80 at 0x40 and returns to its caller.
    // Cover both the fused path and fallback for memory expansion or panic.
    for (bool const initialized_memory : {false, true}) {
        for (uint8_t const overflow_flag : {0, 1}) {
            std::vector<uint8_t> code;
            if (initialized_memory) {
                code = {PUSH1, 0, PUSH1, 0x40, MSTORE};
            }
            code.push_back(PUSH2);
            size_t const return_operand = code.size();
            code.insert(
                code.end(), {0, 0, PUSH1, 0x80, PUSH1, overflow_flag, PUSH8});
            code.insert(code.end(), 8, 0xff);
            code.insert(code.end(), {DUP3, GT, OR, PUSH2});
            size_t const panic_operand = code.size();
            code.insert(code.end(), {0, 0, JUMPI, PUSH1, 0x40, MSTORE, JUMP});
            code[return_operand + 1] = static_cast<uint8_t>(code.size());
            code.insert(
                code.end(),
                {JUMPDEST, PUSH1, 0x40, MLOAD, PUSH1, 0x80, EQ, PUSH2});
            size_t const success_operand = code.size();
            code.insert(code.end(), {0, 0, JUMPI});
            code[panic_operand + 1] = static_cast<uint8_t>(code.size());
            code.insert(code.end(), {JUMPDEST, 0xfe});
            code[success_operand + 1] = static_cast<uint8_t>(code.size());
            code.insert(code.end(), {JUMPDEST, STOP});
            int64_t const cost = initialized_memory ? 93 : 84;
            auto const result = run(code, cost);
            effects &= overflow_flag
                           ? failed_cleanly(result)
                           : result.status == EVMC_SUCCESS && result.gas == 0;
            effects &= failed_cleanly(run(code, cost - 1));
        }
    }
    // Compare batched copies with a byte model that preserves word order,
    // including overlap, partial lengths, zero turns and memory growth.
    for (auto const params : std::array<std::array<unsigned, 4>, 6>{
             {{0, 128, 64, 0},
              {0, 16, 64, 0},
              {16, 0, 64, 0},
              {0, 0, 33, 0},
              {0, 128, 0, 0},
              {0, 128, 65, 32}}}) {
        auto const [src, dst, len, first] = params;
        std::array<uint8_t, 256> expected{};
        std::vector<uint8_t> code;
        for (unsigned word = 0; word < 4; ++word) {
            code.push_back(PUSH32);
            for (unsigned byte = 0; byte < 32; ++byte) {
                uint8_t const v = static_cast<uint8_t>(word * 32 + byte + 1);
                expected[word * 32 + byte] = v;
                code.push_back(v);
            }
            code.insert(
                code.end(), {PUSH1, static_cast<uint8_t>(word * 32), MSTORE});
        }
        unsigned turns = 0;
        for (unsigned i = first; i < len; i += 32) {
            std::array<uint8_t, 32> temp;
            std::copy_n(expected.begin() + src + i, 32, temp.begin());
            std::copy(temp.begin(), temp.end(), expected.begin() + dst + i);
            ++turns;
        }
        for (unsigned v : {len, dst, src, first}) {
            code.insert(
                code.end(),
                {PUSH2, static_cast<uint8_t>(v >> 8), static_cast<uint8_t>(v)});
        }
        size_t const head = code.size();
        code.push_back(JUMPDEST);
        size_t const body = code.size();
        code.insert(
            code.end(),
            {DUP4,
             DUP2,
             LT,
             ISZERO,
             PUSH2,
             0,
             0,
             JUMPI,
             DUP2,
             DUP2,
             ADD,
             MLOAD,
             DUP4,
             DUP3,
             ADD,
             MSTORE,
             PUSH1,
             32,
             ADD,
             PUSH2,
             static_cast<uint8_t>(head >> 8),
             static_cast<uint8_t>(head),
             JUMP});
        code[body + 5] = static_cast<uint8_t>(code.size() >> 8);
        code[body + 6] = static_cast<uint8_t>(code.size());
        code.push_back(JUMPDEST);
        for (unsigned word = 0; word < 8; ++word) {
            code.insert(
                code.end(),
                {PUSH1, static_cast<uint8_t>(word * 32), MLOAD, PUSH32});
            code.insert(
                code.end(),
                expected.begin() + word * 32,
                expected.begin() + (word + 1) * 32);
            code.push_back(EQ);
            size_t const jump = code.size();
            code.insert(code.end(), {PUSH2, 0, 0, JUMPI, 0xfe});
            code[jump + 1] = static_cast<uint8_t>(code.size() >> 8);
            code[jump + 2] = static_cast<uint8_t>(code.size());
            code.push_back(JUMPDEST);
        }
        code.push_back(STOP);
        int64_t const cost = 307 + 67 * turns;
        auto const result = run(code, cost);
        effects &= result.status == EVMC_SUCCESS && result.gas == 0 &&
                   result.accesses == 0;
        effects &= failed_cleanly(run(code, cost - 1));
        effects &= failed_cleanly(run(code, 61)); // OOG at loop entry.
    }
    check(effects);
    // Two selector tests: first match, second match, or neither. Sweep gas
    // through both tests and the taken jump's JUMPDEST charge.
    bool selectors = true;
    for (uint8_t selector = 0; selector <= 2; ++selector) {
        std::array<uint8_t, 27> const code{
            PUSH1, selector, DUP1,  PUSH4, 0,    0,     0,    1,        EQ,
            PUSH2, 0,        25,    JUMPI, DUP1, PUSH4, 0,    0,        0,
            2,     EQ,       PUSH2, 0,     25,   JUMPI, STOP, JUMPDEST, STOP};
        int64_t const cost = selector == 1 ? 26 : selector == 2 ? 48 : 47;
        for (int64_t gas = 0; gas <= 50; ++gas) {
            auto const result = run(code, gas);
            selectors &= gas < cost
                             ? failed_cleanly(result)
                             : result.status == EVMC_SUCCESS &&
                                   result.gas == gas - cost &&
                                   result.refund == 0 && result.output == 0 &&
                                   result.accesses == 0;
        }
    }
    check(selectors);
    // Check every PUSH1 mask width, with and without the optional AND.
    bool masks = true;
    for (unsigned k = 0; k < 256; ++k) {
        std::array<uint8_t, 32> expected{};
        for (unsigned bit = 0; bit < k; ++bit) {
            expected[31 - bit / 8] |= uint8_t{1} << (bit % 8);
        }
        for (bool apply : {false, true}) {
            std::vector<uint8_t> code;
            if (apply) {
                code.push_back(PUSH32);
                code.insert(code.end(), 32, 0xff);
            }
            code.insert(
                code.end(),
                {PUSH1, 1, PUSH1, 1, PUSH1, static_cast<uint8_t>(k), SHL, SUB});
            if (apply) {
                code.push_back(AND);
            }
            code.push_back(PUSH32);
            code.insert(code.end(), expected.begin(), expected.end());
            code.push_back(EQ);
            size_t const jump = code.size();
            code.insert(code.end(), {PUSH2, 0, 0, JUMPI, 0xfe});
            code[jump + 2] = static_cast<uint8_t>(code.size());
            code.insert(code.end(), {JUMPDEST, STOP});
            int64_t const cost = apply ? 41 : 35;
            auto const result = run(code, cost);
            masks &= result.status == EVMC_SUCCESS && result.gas == 0 &&
                     result.output == 0 && result.refund == 0 &&
                     result.accesses == 0;
            masks &= failed_cleanly(run(code, cost - 1));
        }
    }
    check(masks);
    // Nonuniform immediate masks exercise byte order and all word boundaries.
    bool immediate_masks = true;
    for (unsigned width : {4u, 20u}) {
        std::array<uint8_t, 32> value{};
        std::array<uint8_t, 32> mask{};
        std::array<uint8_t, 32> expected{};
        for (unsigned i = 0; i < 32; ++i) {
            value[i] = static_cast<uint8_t>(0xa5 ^ (i * 7));
            if (i >= 32 - width) {
                mask[i] = static_cast<uint8_t>(i * 13 + 1);
            }
            expected[i] = value[i] & mask[i];
        }
        std::vector<uint8_t> code{PUSH32};
        code.insert(code.end(), value.begin(), value.end());
        code.push_back(static_cast<uint8_t>(PUSH0 + width));
        code.insert(code.end(), mask.end() - width, mask.end());
        code.insert(code.end(), {AND, PUSH32});
        code.insert(code.end(), expected.begin(), expected.end());
        code.push_back(EQ);
        size_t const jump = code.size();
        code.insert(code.end(), {PUSH2, 0, 0, JUMPI, 0xfe});
        code[jump + 2] = static_cast<uint8_t>(code.size());
        code.insert(code.end(), {JUMPDEST, STOP});
        auto const result = run(code, 29);
        immediate_masks &= result.status == EVMC_SUCCESS && result.gas == 0 &&
                           result.output == 0 && result.refund == 0 &&
                           result.accesses == 0;
        immediate_masks &= failed_cleanly(run(code, 28));
    }
    check(immediate_masks);
    return failures;
}
