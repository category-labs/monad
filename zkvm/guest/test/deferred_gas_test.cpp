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
    };

    Outcome run(std::span<uint8_t const> code, int64_t gas)
    {
        CountingHost host;
        vm::Message msg{};
        msg.gas = gas;
        auto ctx = runtime::Context::from(host, &msg, code);
        interpreter::Intercode analysis{code};
        std::array<uint256_t, 1024> stack;
        interpreter::execute<GasTraits>(ctx, analysis, stack.data());
        auto result = ctx.copy_to_result<GasTraits>();
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
        return r.status != CallStatus::Success &&
               r.status != CallStatus::Revert && r.gas == 0 && r.refund == 0 &&
               r.output == 0 && r.accesses == 0;
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
                             : result.status == CallStatus::Success &&
                                   result.gas == gas - cost &&
                                   result.refund == 0 && result.output == 0 &&
                                   result.accesses == 0;
        }
    }
    check(selectors);
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
        immediate_masks &= result.status == CallStatus::Success &&
                           result.gas == 0 && result.output == 0 &&
                           result.refund == 0 && result.accesses == 0;
        immediate_masks &= failed_cleanly(run(code, 28));
    }
    check(immediate_masks);
    return failures;
}
