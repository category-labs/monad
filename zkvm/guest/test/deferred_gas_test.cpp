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
#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/types.hpp>

#include <array>
#include <cstdint>
#include <initializer_list>
#include <span>
#include <utility>
#include <vector>

namespace
{
    using namespace monad;
    using namespace monad::vm;
    using enum compiler::EvmOpCode;
    using GasTraits = EvmTraits<EvmRevision::Cancun>;

    // Any callback other than get_tx_context is observable by the witness
    // provider. Count reads as well as writes: a reverted read can still fail
    // when the corresponding proof is absent.
    struct CountingHost final : vm::Host
    {
        mutable unsigned accesses = 0;
        vm::TxContext tx{};

        CountingHost()
        {
            tx.block_number = 1;
        }

        bool account_exists(Address const &) const noexcept override
        {
            ++accesses;
            return false;
        }

        bytes32_t
        get_storage(Address const &, bytes32_t const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        AccessStatus sload_into(
            Address const &, bytes32_t const &, bool,
            uint256_t &out) noexcept override
        {
            ++accesses;
            out = {};
            return AccessStatus::Warm;
        }

        vm::runtime::SstoreStatus sstore_into(
            Address const &, bytes32_t const &, bytes32_t const &,
            bool) noexcept override
        {
            ++accesses;
            return {AccessStatus::Warm, StorageStatus::Assigned};
        }

        std::optional<Address>
        delegate_of(monad_address const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        StorageStatus set_storage(
            Address const &, bytes32_t const &,
            bytes32_t const &) noexcept override
        {
            ++accesses;
            return StorageStatus::Assigned;
        }

        uint256_t get_balance(Address const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        size_t get_code_size(Address const &) const noexcept override
        {
            ++accesses;
            return 0;
        }

        bytes32_t get_code_hash(Address const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        size_t
        copy_code(Address const &, size_t, uint8_t *, size_t) const override
        {
            ++accesses;
            return 0;
        }

        bool selfdestruct(Address const &, Address const &) noexcept override
        {
            ++accesses;
            return false;
        }

        vm::Result call(vm::Message const &) noexcept override
        {
            ++accesses;
            return vm::Result{CallStatus::Failure, 0, 0};
        }

        vm::TxContext const *get_tx_context() const noexcept override
        {
            return &tx;
        }

        bytes32_t get_block_hash(int64_t) const noexcept override
        {
            ++accesses;
            return {};
        }

        void emit_log(
            Address const &, uint8_t const *, size_t, bytes32_t const *,
            size_t) noexcept override
        {
            ++accesses;
        }

        AccessStatus access_account(Address const &) override
        {
            ++accesses;
            return AccessStatus::Warm;
        }

        AccessStatus
        access_storage(Address const &, bytes32_t const &) noexcept override
        {
            ++accesses;
            return AccessStatus::Warm;
        }

        bytes32_t get_transient_storage(
            Address const &, bytes32_t const &) const noexcept override
        {
            ++accesses;
            return {};
        }

        void set_transient_storage(
            Address const &, bytes32_t const &,
            bytes32_t const &) noexcept override
        {
            ++accesses;
        }

        PageStorageStatus update_page(
            Address const &, bytes32_t const &, StorageStatus) noexcept override
        {
            ++accesses;
            return {};
        }
    };

    struct Outcome
    {
        CallStatus status;
        int64_t gas;
        int64_t refund;
        size_t output;
        unsigned accesses;
        std::vector<uint8_t> output_bytes;
    };

    template <typename Traits = GasTraits>
    Outcome
    run(std::span<uint8_t const> code, int64_t gas,
        std::span<uint8_t const> input = {}, uint8_t call_value = 0)
    {
        CountingHost host;
        vm::Message msg{};
        msg.gas = gas;
        msg.value.bytes[31] = call_value;
        msg.input_data = input.data();
        msg.input_size = input.size();
        auto ctx = runtime::Context::from(host, &msg, code);
        interpreter::Intercode analysis{code};
        std::array<uint256_t, runtime::EvmStackAllocatorMeta::size> stack;
        interpreter::execute<Traits>(ctx, analysis, stack.data());
        auto result = ctx.copy_to_result<Traits>();
        return {
            result.status_code,
            result.gas_left,
            result.gas_refund,
            result.output_size,
            host.accesses,
            result.output_size == 0
                ? std::vector<uint8_t>{}
                : std::vector<uint8_t>{
                      result.output_data,
                      result.output_data + result.output_size}};
    }

    bool failed_cleanly(Outcome const &r)
    {
        // A stack error can precede the delayed OOG. Both exceptional statuses
        // must consume all gas, return no data and perform no host access.
        return r.status != CallStatus::Success &&
               r.status != CallStatus::Revert && r.gas == 0 && r.refund == 0 &&
               r.output == 0 && r.accesses == 0;
    }

    bool dup_prefixes()
    {
        for (unsigned depth = 2; depth <= 16; ++depth) {
            for (auto follower :
                 {ADD, SUB, AND, LT, GT, SWAP1, MLOAD, MSTORE, POP}) {
                std::vector<uint8_t> code;
                for (unsigned i = 0; i < 16; ++i) {
                    code.insert(
                        code.end(), {PUSH3, 0, 0, static_cast<uint8_t>(i + 1)});
                }
                code.push_back(static_cast<uint8_t>(DUP1 + depth - 1));
                auto reference = code;
                // JUMPDEST separates DUPn from its follower and costs one gas.
                reference.push_back(JUMPDEST);
                for (auto *program : {&code, &reference}) {
                    program->push_back(static_cast<uint8_t>(follower));
                    program->insert(
                        program->end(),
                        {PUSH2, 0, 64, MSTORE, PUSH1, 96, PUSH0, RETURN});
                }
                auto const expected = run(reference, 1001);
                auto const actual = run(code, 1000);
                if (expected.status != CallStatus::Success ||
                    actual.status != CallStatus::Success ||
                    actual.gas != expected.gas ||
                    actual.output_bytes != expected.output_bytes ||
                    !failed_cleanly(run(code, 999 - actual.gas))) {
                    return false;
                }
            }
        }
        return true;
    }

    bool comparison_prefixes()
    {
        for (auto comparison : {LT, GT, SLT, SGT, EQ, ISZERO}) {
            for (uint8_t operand : {0, 1}) {
                // The high bit catches a partial 256-bit store and
                // distinguishes signed from unsigned comparisons. Keep a second
                // word for OR.
                std::vector<uint8_t> prefix{PUSH32};
                prefix.resize(33, 0);
                prefix[1] = 0x80;
                if (comparison != ISZERO) {
                    prefix.push_back(DUP1);
                }
                if (comparison == EQ && operand == 1) {
                    prefix.push_back(DUP1);
                }
                else {
                    prefix.insert(prefix.end(), {PUSH3, 0, 0, operand});
                }
                prefix.push_back(static_cast<uint8_t>(comparison));
                for (auto follower : {OR, POP, PUSH2, JUMPI, JUMPDEST}) {
                    auto make_program = [&](bool separate) {
                        auto code = prefix;
                        for (unsigned i = 0; i < 7; ++i) {
                            if (separate) {
                                code.push_back(JUMPDEST);
                            }
                            code.push_back(ISZERO);
                        }
                        if (separate) {
                            code.push_back(JUMPDEST);
                        }
                        if (follower == JUMPI) {
                            // The taken path returns a word; the fallthrough
                            // stops.
                            auto const target =
                                static_cast<uint8_t>(code.size() + 5);
                            code.insert(
                                code.end(),
                                {PUSH2,
                                 0,
                                 target,
                                 JUMPI,
                                 STOP,
                                 JUMPDEST,
                                 PUSH1,
                                 9});
                        }
                        else if (follower == PUSH2) {
                            code.insert(code.end(), {PUSH2, 0x12, 0x34, POP});
                        }
                        else {
                            code.push_back(static_cast<uint8_t>(follower));
                        }
                        code.insert(
                            code.end(),
                            {PUSH0, MSTORE, PUSH1, 32, PUSH0, RETURN});
                        return code;
                    };
                    auto const program = make_program(false);
                    auto const actual = run(program, 1000);
                    auto const expected = run(make_program(true), 1008);
                    if (actual.status != CallStatus::Success ||
                        expected.status != CallStatus::Success ||
                        actual.gas != expected.gas ||
                        actual.output_bytes != expected.output_bytes ||
                        !failed_cleanly(run(program, 999 - actual.gas))) {
                        return false;
                    }
                }
            }
        }
        std::vector<uint8_t> full_stack(1024, PUSH0);
        full_stack.insert(
            full_stack.end(), {ISZERO, ISZERO, PUSH2, 0, 0, JUMPI, STOP});
        // The jump below is taken with the inverted comparison result.
        std::array<uint8_t, 8> const invalid_jump{
            PUSH0, PUSH0, LT, ISZERO, PUSH2, 0xff, 0xff, JUMPI};
        return failed_cleanly(run(full_stack, 10000)) &&
               failed_cleanly(run(invalid_jump, 100));
    }

    bool swapn_prefixes()
    {
        for (unsigned depth = 2; depth <= 16; ++depth) {
            for (auto follower : {POP, SWAP1, SWAP2, SWAP3, SWAP4, JUMPDEST}) {
                std::vector<uint8_t> code;
                for (uint8_t word = 1; word <= 17; ++word) {
                    code.insert(code.end(), {PUSH3, 0, 0, word});
                }
                code.push_back(static_cast<uint8_t>(SWAP1 + depth - 1));
                auto reference = code;
                reference.push_back(
                    JUMPDEST); // Execute the two opcodes separately.
                for (auto *program : {&code, &reference}) {
                    program->push_back(static_cast<uint8_t>(follower));
                    // Return every remaining word, including both swap
                    // partners.
                    unsigned const bytes = 32 * (follower == POP ? 16 : 17);
                    for (unsigned offset = 0; offset < bytes; offset += 32) {
                        program->insert(
                            program->end(),
                            {PUSH2,
                             static_cast<uint8_t>(offset >> 8),
                             static_cast<uint8_t>(offset),
                             MSTORE});
                    }
                    program->insert(
                        program->end(),
                        {PUSH2,
                         static_cast<uint8_t>(bytes >> 8),
                         static_cast<uint8_t>(bytes),
                         PUSH0,
                         RETURN});
                }
                auto const expected = run(reference, 1001);
                auto const actual = run(code, 1000);
                if (actual.status != CallStatus::Success ||
                    expected.status != CallStatus::Success ||
                    actual.gas != expected.gas ||
                    actual.output_bytes != expected.output_bytes ||
                    !failed_cleanly(run(code, 999 - actual.gas))) {
                    return false;
                }
            }
        }
        std::array<uint8_t, 6> const short_stack{
            PUSH0, PUSH0, PUSH0, SWAP2, SWAP3, STOP};
        return failed_cleanly(run(short_stack, 100));
    }

    bool full_stack_swaps()
    {
        using Stack = runtime::EvmStackAllocatorMeta;
        constexpr size_t height = Stack::max_stack_height;
        uint256_t const sentinel{std::array<uint64_t, 4>{
            0x0123456789abcdef,
            0xfedcba9876543210,
            0xa5a5a5a5a5a5a5a5,
            0x5a5a5a5a5a5a5a5a}};

        for (bool const followed_by_swap2 : {false, true}) {
            std::vector<uint8_t> code;
            code.insert(code.end(), height - 3, PUSH0);
            std::array<uint256_t, 3> values;
            for (size_t i = 0; i < values.size(); ++i) {
                uint8_t const byte = static_cast<uint8_t>(0x11 * (i + 1));
                uint64_t const word = 0x0101010101010101ULL * byte;
                values[i] =
                    uint256_t{std::array<uint64_t, 4>{word, word, word, word}};
                code.push_back(PUSH32);
                code.insert(code.end(), 32, byte);
            }
            code.push_back(SWAP1);
            if (followed_by_swap2) {
                code.push_back(SWAP2);
            }
            // STOP selects the ordinary SWAP1 prefix, without a push.
            code.push_back(STOP);
            int64_t const gas = static_cast<int64_t>(
                2 * (height - 3) + 9 + 3 + (followed_by_swap2 ? 3 : 0));

            CountingHost host;
            vm::Message msg{};
            msg.gas = gas;
            auto ctx = runtime::Context::from(host, &msg, code);
            interpreter::Intercode analysis{code};
            // Guard the physical allocation, including ZisK's spare slot.
            std::array<uint256_t, Stack::size + 1> stack{};
            stack[Stack::size] = sentinel;
            interpreter::execute<GasTraits>(ctx, analysis, stack.data());
            auto const result = ctx.copy_to_result<GasTraits>();
            std::array<uint256_t, 3> const expected =
                followed_by_swap2 ? std::array{values[1], values[2], values[0]}
                                  : std::array{values[0], values[2], values[1]};
            if (result.status_code != CallStatus::Success ||
                result.gas_left != 0 || host.accesses != 0 ||
                stack[Stack::size] != sentinel) {
                return false;
            }
            for (size_t i = 0; i < height; ++i) {
                uint256_t const value =
                    i < height - 3 ? uint256_t{0} : expected[i - (height - 3)];
                if (stack[i] != value) {
                    return false;
                }
            }
        }
        return true;
    }

    bool swap1_prefixes()
    {
        for (unsigned padding = 0; padding < 7; ++padding) {
            for (auto follower : {PC, POP, DUP2, SWAP2, JUMP}) {
                // Three distinct words, bottom to top. PC POP shifts the lag
                // without changing them. PUSH3 avoids a fused push/swap.
                std::vector<uint8_t> code{
                    PUSH3, 0, 0, 0x11, PUSH3, 0, 0, 0x22, PUSH3, 0, 0, 0x33};
                for (unsigned i = 0; i < padding; ++i) {
                    code.insert(code.end(), {PC, POP});
                }
                code.insert(
                    code.end(), {SWAP1, static_cast<uint8_t>(follower)});
                std::vector<uint8_t> top_first;
                int64_t gas = 9 + 4 * padding + 3;
                switch (follower) {
                case PC:
                    code.push_back(POP);
                    top_first = {0x22, 0x33, 0x11};
                    gas += 4;
                    break;
                case POP:
                    top_first = {0x33, 0x11};
                    gas += 2;
                    break;
                case DUP2:
                    top_first = {0x33, 0x22, 0x33, 0x11};
                    gas += 3;
                    break;
                case SWAP2:
                    top_first = {0x11, 0x33, 0x22};
                    gas += 3;
                    break;
                case JUMP:
                    code.push_back(
                        0xfe); // A failed jump must not fall through.
                    code[7] = static_cast<uint8_t>(code.size());
                    code.push_back(JUMPDEST);
                    top_first = {0x33, 0x11};
                    gas += 9;
                    break;
                default:
                    return false;
                }
                std::vector<uint8_t> expected(32 * top_first.size());
                for (size_t i = 0; i < top_first.size(); ++i) {
                    code.insert(
                        code.end(),
                        {PUSH2, 0, static_cast<uint8_t>(32 * i), MSTORE});
                    expected[32 * i + 31] = top_first[i];
                    gas += 9; // PUSH2, MSTORE and one new memory word.
                }
                code.insert(
                    code.end(),
                    {PUSH2,
                     0,
                     static_cast<uint8_t>(expected.size()),
                     PUSH0,
                     RETURN});
                gas += 5;
                auto const result = run(code, gas);
                if (result.status != CallStatus::Success || result.gas != 0 ||
                    result.output_bytes != expected ||
                    !failed_cleanly(run(code, gas - 1))) {
                    return false;
                }
            }
        }
        std::array<uint8_t, 4> short_swap{PUSH0, PUSH0, SWAP1, SWAP2};
        std::array<uint8_t, 6> bad_jump{
            PUSH0, PUSH0, SWAP1, JUMP, JUMPDEST, STOP};
        std::vector<uint8_t> full_stack(1024, PUSH0);
        full_stack.insert(full_stack.end(), {SWAP1, DUP2, STOP});
        return failed_cleanly(run(short_swap, 100)) &&
               failed_cleanly(run(bad_jump, 100)) &&
               failed_cleanly(run(full_stack, 10000));
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
        boundary &= gas < 11 ? failed_cleanly(r)
                             : r.status == CallStatus::Success &&
                                   r.gas == gas - 11 && r.output == 0 &&
                                   r.refund == 0 && r.accesses == 0;
    }
    // Distinct bytes expose carries and zero-fill around both wide SHR
    // boundaries.
    for (unsigned shift : {127u, 128u, 129u, 191u, 192u, 193u, 255u}) {
        bytes32_t input{};
        for (unsigned i = 0; i < sizeof(input.bytes); ++i) {
            input.bytes[i] = static_cast<uint8_t>(0x81u + i);
        }
        std::vector<uint8_t> code{PUSH32};
        code.insert(code.end(), std::begin(input.bytes), std::end(input.bytes));
        code.insert(
            code.end(), {PUSH1, static_cast<uint8_t>(shift), SHR, PUSH32});
        auto const expected =
            store_be_as<bytes32_t>(load_be<uint256_t>(input) >> shift);
        code.insert(code.end(), expected.bytes, expected.bytes + 32);
        code.insert(code.end(), {EQ, PUSH2, 0, 0, JUMPI, 0xfe});
        code[code.size() - 3] = static_cast<uint8_t>(code.size());
        code.insert(code.end(), {JUMPDEST, STOP});
        auto const result = run(code, 29);
        boundary &= result.status == CallStatus::Success && result.gas == 0;
        boundary &= failed_cleanly(run(code, 28));
    }
    // Exercise all five pair prefixes plus an ordinary fall-through prefix.
    for (auto op : {ADD, SHL, SHR, SAR, PUSH1, POP}) {
        std::vector<uint8_t> code{PUSH0, PUSH1, 1, static_cast<uint8_t>(op)};
        if (op == PUSH1) {
            code.push_back(2);
        }
        code.push_back(STOP);
        int64_t const cost = op == POP ? 7 : 8;
        for (int64_t gas = 0; gas <= cost + 1; ++gas) {
            auto const r = run(code, gas);
            boundary &= gas < cost ? failed_cleanly(r)
                                   : r.status == CallStatus::Success &&
                                         r.gas == gas - cost;
        }
        // The temporary PUSH1 must still overflow a full stack.
        code.insert(code.begin(), 1023, PUSH0);
        boundary &= failed_cleanly(run(code, 10000));
    }
    // Consecutive PUSH1s must charge each immediate and stop at stack capacity.
    for (size_t const count : {1, 2, 3, 1023, 1024, 1025}) {
        std::vector<uint8_t> code;
        for (size_t i = 0; i < count; ++i) {
            code.insert(code.end(), {PUSH1, static_cast<uint8_t>(i)});
        }
        code.push_back(STOP);
        int64_t const cost = 3 * static_cast<int64_t>(count);
        for (int64_t const gas : {int64_t{0}, cost - 1, cost, cost + 1}) {
            auto const result = run(code, gas);
            boundary &= gas < cost || count > 1024
                            ? failed_cleanly(result)
                            : result.status == CallStatus::Success &&
                                  result.gas == gas - cost;
        }
    }
    check(boundary);
    // At exactly the required gas, RETURN and REVERT retain their status.
    std::array<uint8_t, 5> const ret{PUSH1, 0, PUSH1, 0, RETURN};
    std::array<uint8_t, 5> const rev{PUSH1, 0, PUSH1, 0, REVERT};
    auto const r = run(ret, 6);
    auto const v = run(rev, 6);
    check(r.status == CallStatus::Success && r.gas == 0 && r.output == 0);
    check(v.status == CallStatus::Revert && v.gas == 0 && v.output == 0);
    // The extra host-read checkpoints must not reject affordable reads.
    bool reads = true;
    for (auto const [op, cost] : std::array<std::pair<uint8_t, int64_t>, 3>{
             {{BLOCKHASH, 23}, {SELFBALANCE, 8}, {TLOAD, 103}}}) {
        std::array<uint8_t, 4> const code{PUSH1, 0, op, STOP};
        auto const result = run(code, cost);
        reads &= result.status == CallStatus::Success && result.gas == 0 &&
                 result.accesses == 1;
    }
    check(reads);

    bool effects = true;
    // Compare PUSH1 pairs with PUSH2 (same gas, no pair prefix), checking
    // values and every gas budget through the exact success boundary.
    auto const verify_immediate_pair =
        [&](auto const op,
            uint8_t const immediate,
            bool const has_operand,
            std::array<uint8_t, 32> const &operand,
            std::array<uint8_t, 32> const &expected,
            std::span<uint8_t const>
                calldata) {
            for (bool const fused : {false, true}) {
                std::vector<uint8_t> code;
                if (has_operand) {
                    code.push_back(PUSH32);
                    code.insert(code.end(), operand.begin(), operand.end());
                }
                code.push_back(fused ? PUSH1 : PUSH2);
                if (!fused) {
                    code.push_back(0);
                }
                code.insert(
                    code.end(), {immediate, static_cast<uint8_t>(op), PUSH32});
                code.insert(code.end(), expected.begin(), expected.end());
                code.insert(code.end(), {EQ, PUSH2, 0, 0, JUMPI, 0xfe});
                code[code.size() - 3] = static_cast<uint8_t>(code.size());
                code.insert(code.end(), {JUMPDEST, STOP});
                int64_t const cost =
                    20 + (has_operand ? 3 : 0) + 3 + (op == SIGNEXTEND ? 5 : 3);
                for (int64_t gas = 0; gas <= cost + 1; ++gas) {
                    auto const result = run(code, gas, calldata);
                    effects &= gas < cost
                                   ? failed_cleanly(result)
                                   : result.status == CallStatus::Success &&
                                         result.gas == gas - cost;
                }
            }
        };
    // Check no carry, carries across each 64-bit boundary and 256-bit wrap.
    for (uint8_t const immediate : {0, 1, 2, 255}) {
        for (unsigned full_words = 0; full_words <= 4; ++full_words) {
            for (uint8_t const low_byte : {0, 1, 254, 255}) {
                std::array<uint8_t, 32> addend{};
                addend.fill(0x42);
                for (unsigned i = 0; i < full_words * 8; ++i) {
                    addend[31 - i] = 0xff;
                }
                addend[31] = low_byte;
                auto expected = addend;
                unsigned carry = immediate;
                for (unsigned i = 32; i != 0; --i) {
                    unsigned const sum = expected[i - 1] + carry;
                    expected[i - 1] = static_cast<uint8_t>(sum);
                    carry = sum >> 8;
                }
                verify_immediate_pair(
                    ADD, immediate, true, addend, expected, {});
            }
        }
    }
    // PUSH2 must decode both bytes and work with ordinary and fused-PUSH1
    // followers, which use different prefix paths.
    for (unsigned immediate : {0, 1, 255, 256, 0x1234, 65535}) {
        for (bool pair_follower : {false, true}) {
            std::vector<uint8_t> code{
                PUSH2,
                static_cast<uint8_t>(immediate >> 8),
                static_cast<uint8_t>(immediate)};
            if (pair_follower) {
                code.insert(code.end(), {NOT, NOT});
            }
            else {
                code.insert(code.end(), {DUP1, POP});
            }
            code.insert(code.end(), {PUSH0, MSTORE, PUSH1, 32, PUSH0, RETURN});
            std::vector<uint8_t> expected(32);
            expected[30] = static_cast<uint8_t>(immediate >> 8);
            expected[31] = static_cast<uint8_t>(immediate);
            int64_t const cost = pair_follower ? 22 : 21;
            for (int64_t gas = 0; gas <= cost + 1; ++gas) {
                auto const result = run(code, gas);
                effects &= gas < cost ? failed_cleanly(result)
                                      : result.status == CallStatus::Success &&
                                            result.gas == gas - cost &&
                                            result.output_bytes == expected;
            }
        }
    }
    for (auto follower : {STOP, NOT, JUMP, JUMPI}) {
        std::vector<uint8_t> code(1024, PUSH0);
        code.insert(code.end(), {PUSH2, 0, 0, static_cast<uint8_t>(follower)});
        effects &= failed_cleanly(run(code, 10000));
    }
    std::array<uint8_t, 32> operand{};
    operand.fill(0xa5);
    for (uint8_t const immediate :
         {0, 1, 7, 8, 9, 15, 16, 17, 23, 24, 25, 30, 31, 32, 255}) {
        std::array<uint8_t, 32> expected;
        expected.fill(0xff);
        expected.back() = static_cast<uint8_t>(~immediate);
        verify_immediate_pair(NOT, immediate, false, {}, expected, {});
        expected.fill(0);
        expected.back() = operand.back() & immediate;
        verify_immediate_pair(AND, immediate, true, operand, expected, {});
        for (uint8_t const sign_byte : {0x7f, 0x80}) {
            auto signed_operand = operand;
            expected = operand;
            if (immediate < 32) {
                size_t const sign_index = 31 - immediate;
                signed_operand[sign_index] = sign_byte;
                expected = signed_operand;
                for (size_t i = 0; i < sign_index; ++i) {
                    expected[i] = sign_byte & 0x80 ? 0xff : 0;
                }
            }
            verify_immediate_pair(
                SIGNEXTEND, immediate, true, signed_operand, expected, {});
        }
    }
    std::array<uint8_t, 64> calldata;
    for (size_t i = 0; i < calldata.size(); ++i) {
        calldata[i] = static_cast<uint8_t>(i + 1);
    }
    for (size_t const length : {0, 1, 31, 32, 33, 64}) {
        for (uint8_t const offset : {0, 1, 31, 32, 63, 64, 255}) {
            std::array<uint8_t, 32> expected{};
            for (size_t i = 0; i < expected.size() && offset + i < length;
                 ++i) {
                expected[i] = calldata[offset + i];
            }
            verify_immediate_pair(
                CALLDATALOAD,
                offset,
                false,
                {},
                expected,
                std::span{calldata}.first(length));
        }
    }
    for (auto const op : {NOT, AND, SIGNEXTEND, CALLDATALOAD}) {
        if (op == AND || op == SIGNEXTEND) {
            std::array<uint8_t, 4> const code{
                PUSH1, 0, static_cast<uint8_t>(op), STOP};
            effects &= failed_cleanly(run(code, 100));
        }
        std::vector<uint8_t> code(1024, PUSH0);
        code.insert(code.end(), {PUSH1, 0, static_cast<uint8_t>(op), STOP});
        effects &= failed_cleanly(run(code, 10000));
    }
    // Compare fused swaps with ordinary PUSH2 + SWAP, including missing
    // operands and every gas budget through successful execution.
    for (unsigned depth = 1; depth <= 4; ++depth) {
        for (unsigned count = 0; count <= 5; ++count) {
            std::vector<uint8_t> fused;
            for (unsigned value = 1; value <= count; ++value) {
                fused.insert(
                    fused.end(), {PUSH2, 0, static_cast<uint8_t>(value)});
            }
            auto ordinary = fused;
            auto const swap = static_cast<uint8_t>(SWAP1 + depth - 1);
            fused.insert(fused.end(), {PUSH1, 0xa5, swap});
            ordinary.insert(ordinary.end(), {PUSH2, 0, 0xa5, swap});
            // Return every resulting word so misplaced values are observable.
            for (unsigned word = 0; word <= count; ++word) {
                for (auto *code : {&fused, &ordinary}) {
                    code->insert(
                        code->end(),
                        {PUSH2, 0, static_cast<uint8_t>(32 * word), MSTORE});
                }
            }
            for (auto *code : {&fused, &ordinary}) {
                code->insert(
                    code->end(),
                    {PUSH2,
                     0,
                     static_cast<uint8_t>(32 * (count + 1)),
                     PUSH0,
                     RETURN});
            }
            auto const successful = run(fused, 120);
            effects &= count >= depth ? successful.status == CallStatus::Success
                                      : failed_cleanly(successful);
            if (count >= depth) {
                std::vector<uint8_t> expected_bytes(32 * (count + 1));
                for (unsigned word = 0; word <= count; ++word) {
                    expected_bytes[32 * word + 31] = static_cast<uint8_t>(
                        word == 0 ? count - depth + 1
                                  : (word == depth ? 0xa5 : count - word + 1));
                }
                effects &= successful.output_bytes == expected_bytes;
            }
            for (int64_t gas = 0; gas <= 120; ++gas) {
                auto const actual = run(fused, gas);
                auto const expected = run(ordinary, gas);
                effects &= actual.status == expected.status &&
                           actual.gas == expected.gas &&
                           actual.output_bytes == expected.output_bytes;
            }
        }
        std::vector<uint8_t> full(1024, PUSH0);
        full.insert(
            full.end(),
            {PUSH1, 1, static_cast<uint8_t>(SWAP1 + depth - 1), STOP});
        effects &= failed_cleanly(run(full, 10000));
    }
    // Exercise immediate memory pairs with and without expansion, including
    // unaligned offsets and exact gas boundaries. Verify the stored value.
    for (bool const initialized_memory : {false, true}) {
        for (uint8_t const offset : {0, 31, 64, 255}) {
            std::vector<uint8_t> code;
            if (initialized_memory) {
                code = {PUSH0, PUSH2, 1, 0, MSTORE}; // Expand to 288 bytes.
            }
            code.insert(
                code.end(),
                {PUSH1,
                 0xa5,
                 PUSH1,
                 offset,
                 MSTORE,
                 PUSH1,
                 offset,
                 MLOAD,
                 PUSH1,
                 0xa5,
                 EQ,
                 PUSH2,
                 0,
                 0,
                 JUMPI,
                 0xfe});
            code[code.size() - 3] = static_cast<uint8_t>(code.size());
            code.insert(code.end(), {JUMPDEST, STOP});
            int64_t const memory_words =
                (static_cast<int64_t>(offset) + 63) / 32;
            int64_t const cost =
                35 + (initialized_memory ? 35 : 3 * memory_words);
            for (int64_t gas = 0; gas <= cost + 1; ++gas) {
                auto const result = run(code, gas);
                effects &= gas < cost ? failed_cleanly(result)
                                      : result.status == CallStatus::Success &&
                                            result.gas == gas - cost;
            }
        }
    }
    // Compare PUSH2 memory pairs with unfused PUSH3 at two-byte offsets.
    for (unsigned offset : {0, 31, 255, 256, 4095, 65535}) {
        for (bool warm : {false, true}) {
            for (uint8_t push_opcode : {PUSH2, PUSH3}) {
                std::vector<uint8_t> code;
                auto const push_offset = [&] {
                    code.push_back(push_opcode);
                    if (push_opcode == PUSH3) {
                        code.push_back(0);
                    }
                    code.insert(
                        code.end(),
                        {static_cast<uint8_t>(offset >> 8),
                         static_cast<uint8_t>(offset)});
                };
                if (warm) {
                    code.push_back(PUSH0);
                    push_offset();
                    code.push_back(MSTORE);
                }
                code.insert(code.end(), {PUSH1, 0xa5});
                push_offset();
                code.push_back(MSTORE);
                push_offset();
                code.insert(
                    code.end(),
                    {MLOAD, PUSH0, MSTORE, PUSH1, 32, PUSH0, RETURN});
                int64_t const words = (offset + 63) / 32;
                int64_t const cost =
                    25 + (warm ? 8 : 0) + 3 * words + words * words / 512;
                std::vector<uint8_t> expected(32);
                expected.back() = 0xa5;
                for (int64_t gas :
                     {int64_t{0},
                      int64_t{2},
                      int64_t{3},
                      int64_t{5},
                      int64_t{6},
                      cost - 1,
                      cost,
                      cost + 1}) {
                    auto const result = run(code, gas);
                    effects &= gas < cost
                                   ? failed_cleanly(result)
                                   : result.status == CallStatus::Success &&
                                         result.gas == gas - cost &&
                                         result.output_bytes == expected;
                }
            }
        }
    }
    std::vector<uint8_t> push2_memory_stack{PUSH0, PUSH2, 0, 0, MSTORE};
    push2_memory_stack.insert(
        push2_memory_stack.end(), {PUSH2, 0, 0, MSTORE, STOP});
    effects &= failed_cleanly(run(push2_memory_stack, 10000));
    for (auto op : {MLOAD, MSTORE}) {
        push2_memory_stack = {PUSH0, PUSH2, 0, 0, MSTORE};
        push2_memory_stack.insert(push2_memory_stack.end(), 1024, PUSH0);
        push2_memory_stack.insert(
            push2_memory_stack.end(),
            {PUSH2, 0, 0, static_cast<uint8_t>(op), STOP});
        effects &= failed_cleanly(run(push2_memory_stack, 10000));
    }
    // A warm memory range must not hide a missing MSTORE value or a full stack.
    std::vector<uint8_t> memory_stack{PUSH0, PUSH1, 0, MSTORE};
    memory_stack.insert(memory_stack.end(), {PUSH1, 0, MSTORE, STOP});
    effects &= failed_cleanly(run(memory_stack, 10000));
    for (auto const op : {MLOAD, MSTORE}) {
        memory_stack = {PUSH0, PUSH1, 0, MSTORE};
        memory_stack.insert(memory_stack.end(), 1024, PUSH0);
        memory_stack.insert(
            memory_stack.end(), {PUSH1, 0, static_cast<uint8_t>(op), STOP});
        effects &= failed_cleanly(run(memory_stack, 10000));
    }
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
            effects &= overflow_flag ? failed_cleanly(result)
                                     : result.status == CallStatus::Success &&
                                           result.gas == 0;
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
        effects &= result.status == CallStatus::Success && result.gas == 0 &&
                   result.accesses == 0;
        effects &= failed_cleanly(run(code, cost - 1));
        effects &= failed_cleanly(run(code, 61)); // OOG at loop entry.
    }
    check(
        effects && full_stack_swaps() && swap1_prefixes() && dup_prefixes() &&
        swapn_prefixes() && comparison_prefixes());
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
                             : result.status == CallStatus::Success &&
                                   result.gas == gas - cost &&
                                   result.refund == 0 && result.output == 0 &&
                                   result.accesses == 0;
        }
    }
    // Exercise both prologues and all three selector encodings at every gas
    // boundary. The bytecode checks the extracted value before stopping.
    std::array<uint8_t, 8> const input{0x12, 0x34, 0x56, 0x78, 0, 0, 0, 0};
    auto patch_jump = [](std::vector<uint8_t> &code, size_t push) {
        code[push + 1] = static_cast<uint8_t>(code.size() >> 8);
        code[push + 2] = static_cast<uint8_t>(code.size());
    };
    auto expect_top = [&](std::vector<uint8_t> &code, uint256_t value) {
        code.push_back(PUSH32);
        for (unsigned i = 32; i != 0; --i) {
            code.push_back(static_cast<uint8_t>(
                value[(i - 1) / 8] >> (8 * ((i - 1) % 8))));
        }
        code.push_back(EQ);
        size_t const jump = code.size();
        code.insert(code.end(), {PUSH2, 0, 0, JUMPI, 0xfe});
        patch_jump(code, jump);
        code.insert(code.end(), {JUMPDEST, STOP});
    };
    bool extraction = true;
    for (bool taken : {false, true}) {
        for (unsigned form = 0; form != 3; ++form) {
            std::vector<uint8_t> code{PUSH1, 4, CALLDATASIZE, LT};
            if (taken) {
                code.push_back(ISZERO);
            }
            size_t const branch = code.size();
            code.insert(code.end(), {PUSH2, 0, 0, JUMPI});
            if (taken) {
                code.push_back(STOP);
                patch_jump(code, branch);
                code.push_back(JUMPDEST);
            }
            if (form == 0) {
                code.push_back(PUSH0);
            }
            else {
                code.insert(code.end(), {PUSH1, 0});
            }
            code.push_back(CALLDATALOAD);
            if (form < 2) {
                code.insert(code.end(), {PUSH1, 224, SHR});
            }
            else {
                code.insert(code.end(), {PUSH29, 1});
                code.insert(code.end(), 28, 0);
                code.insert(
                    code.end(), {SWAP1, DIV, PUSH4, 255, 255, 255, 255, AND});
            }
            expect_top(code, uint256_t{0x12345678});
            if (!taken) {
                patch_jump(code, branch);
                code.insert(code.end(), {JUMPDEST, STOP});
            }
            int64_t const cost = (taken ? 25 : 21) +
                                 (form == 0   ? 11
                                  : form == 1 ? 12
                                              : 23) +
                                 20;
            for (int64_t gas = 0; gas <= cost + 1; ++gas) {
                auto const r = run(code, gas, input);
                extraction &= gas < cost ? failed_cleanly(r)
                                         : r.status == CallStatus::Success &&
                                               r.gas == gas - cost;
            }
            for (size_t len = 0; len < 4; ++len) {
                auto const r = run(code, 100, std::span{input}.first(len));
                extraction &= r.status == CallStatus::Success &&
                              r.gas == 100 - (taken ? 24 : 22);
            }
            if (form == 0) {
                extraction &= failed_cleanly(
                    run<EvmTraits<EvmRevision::Berlin>>(code, 100, input));
            }
        }
    }
    // Truncated extraction must fall back without a 41-byte DMA read beyond
    // the bytecode padding. An incomplete PUSH reads zero-padded immediates.
    for (bool const long_prefix : {false, true}) {
        std::vector<uint8_t> code{
            PUSH1, 4, CALLDATASIZE, LT, PUSH2, 0, 0, JUMPI, PUSH1};
        if (long_prefix) {
            code.insert(code.end(), {0, CALLDATALOAD, PUSH29, 1});
            code.insert(code.end(), 28, 0);
            code.insert(code.end(), {SWAP1, DIV, PUSH4, 255, 255, 255, 255});
        }
        int64_t const cost = long_prefix ? 41 : 24;
        auto const result = run(code, cost, input);
        extraction &= result.status == CallStatus::Success && result.gas == 0;
        extraction &= failed_cleanly(run(code, cost - 1, input));
    }
    // One spare slot suffices for selector extraction; a full stack must fail.
    for (size_t height : {size_t{1023}, size_t{1024}}) {
        std::vector<uint8_t> code(height - 1, PUSH0);
        code.insert(
            code.end(),
            {PUSH1,
             4,
             CALLDATASIZE,
             LT,
             PUSH2,
             0,
             0,
             JUMPI,
             PUSH0,
             CALLDATALOAD,
             PUSH1,
             224,
             SHR,
             STOP});
        auto const r = run(code, 10000, input);
        extraction &= height == 1023 ? r.status == CallStatus::Success
                                     : failed_cleanly(r);
    }
    std::array<uint8_t, 7> const empty_selector{
        CALLDATASIZE, LT, PUSH2, 0, 0, JUMPI, STOP};
    extraction &= failed_cleanly(run(empty_selector, 100, input));

    // Sweep the ABI bounds check's gas; check the computed remainder too.
    bool bounds = true;
    for (uint8_t offset : {uint8_t{0}, uint8_t{4}, uint8_t{9}}) {
        std::vector<uint8_t> code{
            PUSH1,
            offset,
            CALLDATASIZE,
            SUB,
            PUSH1,
            4,
            DUP2,
            LT,
            ISZERO,
            PUSH2,
            0,
            14,
            JUMPI,
            0xfe,
            JUMPDEST};
        expect_top(code, uint256_t{input.size()} - offset);
        for (int64_t gas = 0; gas <= 55; ++gas) {
            auto const r = run(code, gas, input);
            bounds &=
                gas < 54 ? failed_cleanly(r)
                         : r.status == CallStatus::Success && r.gas == gas - 54;
        }
    }
    // The ABI sequence needs two spare slots for PUSH1 followed by DUP2.
    for (size_t height : {size_t{1022}, size_t{1023}}) {
        std::vector<uint8_t> code(height - 1, PUSH0);
        code.insert(
            code.end(),
            {PUSH1, 0, CALLDATASIZE, SUB, PUSH1, 4, DUP2, LT, ISZERO});
        size_t const jump = code.size();
        code.insert(code.end(), {PUSH2, 0, 0, JUMPI, 0xfe});
        patch_jump(code, jump);
        code.insert(code.end(), {JUMPDEST, STOP});
        auto const r = run(code, 10000, input);
        bounds &= height == 1022 ? r.status == CallStatus::Success
                                 : failed_cleanly(r);
    }
    std::array<uint8_t, 12> const empty_bounds{
        CALLDATASIZE,
        SUB,
        PUSH1,
        4,
        DUP2,
        LT,
        ISZERO,
        PUSH2,
        0,
        0,
        JUMPI,
        STOP};
    bounds &= failed_cleanly(run(empty_bounds, 100, input));
    // Non-payable checks: zero value takes the fast path; nonzero reverts.
    for (bool const push_zero : {false, true}) {
        uint8_t const success_pc = push_zero ? 10 : 11;
        std::vector<uint8_t> code{
            CALLVALUE, DUP1, ISZERO, PUSH2, 0, success_pc, JUMPI};
        if (push_zero) {
            code.push_back(PUSH0);
        }
        else {
            code.insert(code.end(), {PUSH1, 0});
        }
        code.insert(code.end(), {DUP1, REVERT, JUMPDEST, POP, STOP});
        for (int64_t gas = 0; gas <= 25; ++gas) {
            auto const result = run(code, gas);
            extraction &= gas < 24 ? failed_cleanly(result)
                                   : result.status == CallStatus::Success &&
                                         result.gas == gas - 24;
        }
        extraction &= run(code, 100, {}, 1).status == CallStatus::Revert;
    }
    for (bool const push_zero : {false, true}) {
        std::vector<uint8_t> code{CALLVALUE, PUSH2, 0, 0, JUMPI};
        if (push_zero) {
            code.push_back(PUSH0);
        }
        else {
            code.insert(code.end(), {PUSH1, 4});
        }
        code.insert(code.end(), {CALLDATASIZE, PUSH1, 3, NOT, ADD, SLT});
        size_t const bound_branch = code.size();
        code.insert(code.end(), {PUSH2, 0, 0, JUMPI, STOP});
        patch_jump(code, 1);
        patch_jump(code, bound_branch);
        code.insert(code.end(), {JUMPDEST, PUSH1, 0, DUP1, REVERT});
        int64_t const cost = push_zero ? 44 : 45;
        for (int64_t gas = 0; gas <= cost + 1; ++gas) {
            auto const result = run(code, gas, input);
            extraction &= gas < cost ? failed_cleanly(result)
                                     : result.status == CallStatus::Success &&
                                           result.gas == gas - cost;
        }
        extraction &= run(code, 100, input, 1).status == CallStatus::Revert;
        extraction &= run(code, 100, std::span{input}.first(3)).status ==
                      CallStatus::Revert;
        auto const berlin =
            run<EvmTraits<EvmRevision::Berlin>>(code, 100, input);
        extraction &= push_zero ? failed_cleanly(berlin)
                                : berlin.status == CallStatus::Success;
    }
    check(selectors && extraction && bounds);
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
            masks &= result.status == CallStatus::Success && result.gas == 0 &&
                     result.output == 0 && result.refund == 0 &&
                     result.accesses == 0;
            for (int64_t gas = 0; gas < cost; ++gas) {
                masks &= failed_cleanly(run(code, gas));
            }
        }
    }
    // Omitting the stores must not omit the temporary stack growth checks.
    for (unsigned initial_size : {1021, 1022, 1023, 1024}) {
        std::vector<uint8_t> code(initial_size, PUSH0);
        code.insert(
            code.end(), {PUSH1, 1, PUSH1, 1, PUSH1, 160, SHL, SUB, STOP});
        auto const result = run(code, 10000);
        masks &= initial_size == 1021 ? result.status == CallStatus::Success
                                      : failed_cleanly(result);
    }
    std::array<uint8_t, 10> const missing_mask_operand{
        PUSH1, 1, PUSH1, 1, PUSH1, 160, SHL, SUB, AND, STOP};
    masks &= failed_cleanly(run(missing_mask_operand, 100));
    check(masks);
    // Nonuniform immediate masks exercise byte order and all word boundaries.
    bool immediate_masks = true;
    for (auto const &[width, all_ones] :
         {std::pair{4u, false}, std::pair{20u, false}, std::pair{20u, true}}) {
        std::array<uint8_t, 32> value{};
        std::array<uint8_t, 32> mask{};
        std::array<uint8_t, 32> expected{};
        for (unsigned i = 0; i < 32; ++i) {
            value[i] = static_cast<uint8_t>(0xa5 ^ (i * 7));
            if (i >= 32 - width) {
                mask[i] = all_ones ? 0xff : static_cast<uint8_t>(i * 13 + 1);
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
        immediate_masks &= result.status == CallStatus::Success &&
                           result.gas == 0 && result.output == 0 &&
                           result.refund == 0 && result.accesses == 0;
        immediate_masks &= failed_cleanly(run(code, 28));
    }
    check(immediate_masks);
    return failures;
}
