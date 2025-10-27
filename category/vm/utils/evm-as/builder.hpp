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

#include <category/vm/core/assert.h>
#include <category/vm/core/cases.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/uint256.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/utils.hpp>

#include <evmc/evmc.h>

#include <concepts>
#include <cstdint>
#include <iterator>
#include <limits>
#include <map>
#include <set>
#include <string>
#include <variant>
#include <vector>

namespace monad::vm::utils::evm_as
{
    template <Traits traits>
    class EvmBuilder
    {
    public:
        EvmBuilder() = default;

        EvmBuilder(EvmBuilder const &prefix, EvmBuilder const &suffix)
        {
            ins_.insert(ins_.begin(), prefix.ins_.begin(), prefix.ins_.end());
            ins_.insert(ins_.end(), suffix.ins_.begin(), suffix.ins_.end());
        }

        compiler::OpCodeInfo const &
        lookup(compiler::EvmOpCode opcode) const noexcept
        {
            return compiler::opcode_table<traits>[opcode];
        }

        EvmBuilder compose(EvmBuilder const &suffix) const noexcept
        {
            return EvmBuilder<traits>(*this, suffix);
        }

        EvmBuilder &append(EvmBuilder const suffix) noexcept
        {
            ins_.insert(ins_.end(), suffix.ins_.begin(), suffix.ins_.end());
            return *this;
        }

        // Iterator interface
        Instructions::const_iterator begin() const
        {
            return ins_.begin();
        }

        Instructions::const_iterator end() const
        {
            return ins_.end();
        }

        size_t size() const
        {
            return ins_.size();
        }

        Instruction::T const &operator[](size_t index) const
        {
            return ins_[index];
        }

        // Inserts a nullary opcode
        EvmBuilder &ins(compiler::EvmOpCode opcode) noexcept
        {
            if (compiler::is_unknown_opcode_info<traits>(
                    compiler::opcode_table<traits>[opcode])) {
                return insert(InvalidI{
                    std::format("0x{:X}", static_cast<uint8_t>(opcode))});
            }
            return insert(PlainI{opcode});
        }

        EvmBuilder &push0() noexcept
        {
            return ins(compiler::EvmOpCode::PUSH0);
        }

        EvmBuilder &spush(int64_t const imm) noexcept
        {
            if (imm < 0) {
                runtime::uint256_t const x{imm};
                return push(runtime::signextend(7, imm));
            }
            return push(static_cast<uint64_t>(imm));
        }

        EvmBuilder &push(uint64_t const imm) noexcept
        {
            size_t n = byte_width(imm);
            MONAD_VM_ASSERT(n <= 32);
            return push(n, runtime::uint256_t{imm});
        }

        EvmBuilder &push(runtime::uint256_t const &imm) noexcept
        {
            size_t n = byte_width(imm);
            MONAD_VM_ASSERT(n <= 32);
            return push(n, imm);
        }

        EvmBuilder &push(size_t n_bytes, runtime::uint256_t const &imm) noexcept
        {
            if (n_bytes > 32) {
                return insert(InvalidI{std::format("PUSH{}", n_bytes)});
            }
            size_t n = n_bytes;
            runtime::uint256_t i = imm;
            if (n_bytes == 0) {
                if (traits::evm_rev() >= EVMC_SHANGHAI) {
                    return push0();
                }
                n = 1;
                i = 0;
            }
            auto const pushop =
                PushI{static_cast<compiler::EvmOpCode>(0x60 + (n - 1)), i};
            return insert(std::move(pushop));
        }

        EvmBuilder &push(std::string const &label) noexcept
        {
            auto const pushop = PushLabelI{label};
            return insert(std::move(pushop));
        }

        EvmBuilder &jumpdest(std::string const &label) noexcept
        {
            auto const jumpdestop = JumpdestI{label};
            return insert(std::move(jumpdestop));
        }

        EvmBuilder &jump(std::string const &label) noexcept
        {
            push(label);
            return ins(compiler::EvmOpCode::JUMP);
        }

        EvmBuilder &jumpi(std::string const &label) noexcept
        {
            push(label);
            return ins(compiler::EvmOpCode::JUMPI);
        }

        EvmBuilder &dup(size_t n) noexcept
        {
            if (n == 0 || n > 16) {
                return insert(InvalidI{std::format("DUP{}", n)});
            }
            auto const opcode =
                compiler::EvmOpCode::DUP1 + static_cast<uint8_t>(n - 1);
            return ins(static_cast<compiler::EvmOpCode>(opcode));
        }

        EvmBuilder &swap(size_t n) noexcept
        {
            if (n == 0 || n > 16) {
                return insert(InvalidI{std::format("SWAP{}", n)});
            }
            auto const opcode =
                compiler::EvmOpCode::SWAP1 + static_cast<uint8_t>(n - 1);
            return ins(static_cast<compiler::EvmOpCode>(opcode));
        }

        EvmBuilder &comment(std::string const &comment) noexcept
        {
            auto commentop = CommentI{comment};
            return insert(std::move(commentop));
        }

        // Boilerplate API
        EvmBuilder &stop() noexcept
        {
            return ins(compiler::EvmOpCode::STOP);
        }

        EvmBuilder &add() noexcept
        {
            return ins(compiler::EvmOpCode::ADD);
        }

        EvmBuilder &mul() noexcept
        {
            return ins(compiler::EvmOpCode::MUL);
        }

        EvmBuilder &sub() noexcept
        {
            return ins(compiler::EvmOpCode::SUB);
        }

        EvmBuilder &div() noexcept
        {
            return ins(compiler::EvmOpCode::DIV);
        }

        EvmBuilder &sdiv() noexcept
        {
            return ins(compiler::EvmOpCode::SDIV);
        }

        EvmBuilder &mod() noexcept
        {
            return ins(compiler::EvmOpCode::MOD);
        }

        EvmBuilder &smod() noexcept
        {
            return ins(compiler::EvmOpCode::SMOD);
        }

        EvmBuilder &addmod() noexcept
        {
            return ins(compiler::EvmOpCode::ADDMOD);
        }

        EvmBuilder &mulmod() noexcept
        {
            return ins(compiler::EvmOpCode::MULMOD);
        }

        EvmBuilder &exp() noexcept
        {
            return ins(compiler::EvmOpCode::EXP);
        }

        EvmBuilder &signextend() noexcept
        {
            return ins(compiler::EvmOpCode::SIGNEXTEND);
        }

        EvmBuilder &lt() noexcept
        {
            return ins(compiler::EvmOpCode::LT);
        }

        EvmBuilder &gt() noexcept
        {
            return ins(compiler::EvmOpCode::GT);
        }

        EvmBuilder &slt() noexcept
        {
            return ins(compiler::EvmOpCode::SLT);
        }

        EvmBuilder &sgt() noexcept
        {
            return ins(compiler::EvmOpCode::SGT);
        }

        EvmBuilder &eq() noexcept
        {
            return ins(compiler::EvmOpCode::EQ);
        }

        EvmBuilder &iszero() noexcept
        {
            return ins(compiler::EvmOpCode::ISZERO);
        }

        EvmBuilder &and_() noexcept
        {
            return ins(compiler::EvmOpCode::AND);
        }

        EvmBuilder &or_() noexcept
        {
            return ins(compiler::EvmOpCode::OR);
        }

        EvmBuilder &xor_() noexcept
        {
            return ins(compiler::EvmOpCode::XOR);
        }

        EvmBuilder &not_() noexcept
        {
            return ins(compiler::EvmOpCode::NOT);
        }

        EvmBuilder &byte() noexcept
        {
            return ins(compiler::EvmOpCode::BYTE);
        }

        EvmBuilder &shl() noexcept
        {
            return ins(compiler::EvmOpCode::SHL);
        }

        EvmBuilder &shr() noexcept
        {
            return ins(compiler::EvmOpCode::SHR);
        }

        EvmBuilder &sar() noexcept
        {
            return ins(compiler::EvmOpCode::SAR);
        }

        EvmBuilder &sha3() noexcept
        {
            return ins(compiler::EvmOpCode::SHA3);
        }

        EvmBuilder &address() noexcept
        {
            return ins(compiler::EvmOpCode::ADDRESS);
        }

        EvmBuilder &balance() noexcept
        {
            return ins(compiler::EvmOpCode::BALANCE);
        }

        EvmBuilder &origin() noexcept
        {
            return ins(compiler::EvmOpCode::ORIGIN);
        }

        EvmBuilder &caller() noexcept
        {
            return ins(compiler::EvmOpCode::CALLER);
        }

        EvmBuilder &callvalue() noexcept
        {
            return ins(compiler::EvmOpCode::CALLVALUE);
        }

        EvmBuilder &calldataload() noexcept
        {
            return ins(compiler::EvmOpCode::CALLDATALOAD);
        }

        EvmBuilder &calldatasize() noexcept
        {
            return ins(compiler::EvmOpCode::CALLDATASIZE);
        }

        EvmBuilder &calldatacopy() noexcept
        {
            return ins(compiler::EvmOpCode::CALLDATACOPY);
        }

        EvmBuilder &codesize() noexcept
        {
            return ins(compiler::EvmOpCode::CODESIZE);
        }

        EvmBuilder &codecopy() noexcept
        {
            return ins(compiler::EvmOpCode::CODECOPY);
        }

        EvmBuilder &gasprice() noexcept
        {
            return ins(compiler::EvmOpCode::GASPRICE);
        }

        EvmBuilder &extcodesize() noexcept
        {
            return ins(compiler::EvmOpCode::EXTCODESIZE);
        }

        EvmBuilder &extcodecopy() noexcept
        {
            return ins(compiler::EvmOpCode::EXTCODECOPY);
        }

        EvmBuilder &returndatasize() noexcept
        {
            return ins(compiler::EvmOpCode::RETURNDATASIZE);
        }

        EvmBuilder &returndatacopy() noexcept
        {
            return ins(compiler::EvmOpCode::RETURNDATACOPY);
        }

        EvmBuilder &extcodehash() noexcept
        {
            return ins(compiler::EvmOpCode::EXTCODEHASH);
        }

        EvmBuilder &blockhash() noexcept
        {
            return ins(compiler::EvmOpCode::BLOCKHASH);
        }

        EvmBuilder &coinbase() noexcept
        {
            return ins(compiler::EvmOpCode::COINBASE);
        }

        EvmBuilder &timestamp() noexcept
        {
            return ins(compiler::EvmOpCode::TIMESTAMP);
        }

        EvmBuilder &number() noexcept
        {
            return ins(compiler::EvmOpCode::NUMBER);
        }

        EvmBuilder &difficulty() noexcept
        {
            return ins(compiler::EvmOpCode::DIFFICULTY);
        }

        EvmBuilder &gaslimit() noexcept
        {
            return ins(compiler::EvmOpCode::GASLIMIT);
        }

        EvmBuilder &chainid() noexcept
        {
            return ins(compiler::EvmOpCode::CHAINID);
        }

        EvmBuilder &selfbalance() noexcept
        {
            return ins(compiler::EvmOpCode::SELFBALANCE);
        }

        EvmBuilder &basefee() noexcept
        {
            return ins(compiler::EvmOpCode::BASEFEE);
        }

        EvmBuilder &blobhash() noexcept
        {
            return ins(compiler::EvmOpCode::BLOBHASH);
        }

        EvmBuilder &blobbasefee() noexcept
        {
            return ins(compiler::EvmOpCode::BLOBBASEFEE);
        }

        EvmBuilder &pop() noexcept
        {
            return ins(compiler::EvmOpCode::POP);
        }

        EvmBuilder &mload() noexcept
        {
            return ins(compiler::EvmOpCode::MLOAD);
        }

        EvmBuilder &mstore() noexcept
        {
            return ins(compiler::EvmOpCode::MSTORE);
        }

        EvmBuilder &mstore8() noexcept
        {
            return ins(compiler::EvmOpCode::MSTORE8);
        }

        EvmBuilder &sload() noexcept
        {
            return ins(compiler::EvmOpCode::SLOAD);
        }

        EvmBuilder &sstore() noexcept
        {
            return ins(compiler::EvmOpCode::SSTORE);
        }

        EvmBuilder &jump() noexcept
        {
            return ins(compiler::EvmOpCode::JUMP);
        }

        EvmBuilder &jumpi() noexcept
        {
            return ins(compiler::EvmOpCode::JUMPI);
        }

        EvmBuilder &pc() noexcept
        {
            return ins(compiler::EvmOpCode::PC);
        }

        EvmBuilder &msize() noexcept
        {
            return ins(compiler::EvmOpCode::MSIZE);
        }

        EvmBuilder &gas() noexcept
        {
            return ins(compiler::EvmOpCode::GAS);
        }

        EvmBuilder &jumpdest() noexcept
        {
            return ins(compiler::EvmOpCode::JUMPDEST);
        }

        EvmBuilder &tload() noexcept
        {
            return ins(compiler::EvmOpCode::TLOAD);
        }

        EvmBuilder &tstore() noexcept
        {
            return ins(compiler::EvmOpCode::TSTORE);
        }

        EvmBuilder &mcopy() noexcept
        {
            return ins(compiler::EvmOpCode::MCOPY);
        }

        EvmBuilder &dup1() noexcept
        {
            return ins(compiler::EvmOpCode::DUP1);
        }

        EvmBuilder &dup2() noexcept
        {
            return ins(compiler::EvmOpCode::DUP2);
        }

        EvmBuilder &dup3() noexcept
        {
            return ins(compiler::EvmOpCode::DUP3);
        }

        EvmBuilder &dup4() noexcept
        {
            return ins(compiler::EvmOpCode::DUP4);
        }

        EvmBuilder &dup5() noexcept
        {
            return ins(compiler::EvmOpCode::DUP5);
        }

        EvmBuilder &dup6() noexcept
        {
            return ins(compiler::EvmOpCode::DUP6);
        }

        EvmBuilder &dup7() noexcept
        {
            return ins(compiler::EvmOpCode::DUP7);
        }

        EvmBuilder &dup8() noexcept
        {
            return ins(compiler::EvmOpCode::DUP8);
        }

        EvmBuilder &dup9() noexcept
        {
            return ins(compiler::EvmOpCode::DUP9);
        }

        EvmBuilder &dup10() noexcept
        {
            return ins(compiler::EvmOpCode::DUP10);
        }

        EvmBuilder &dup11() noexcept
        {
            return ins(compiler::EvmOpCode::DUP11);
        }

        EvmBuilder &dup12() noexcept
        {
            return ins(compiler::EvmOpCode::DUP12);
        }

        EvmBuilder &dup13() noexcept
        {
            return ins(compiler::EvmOpCode::DUP13);
        }

        EvmBuilder &dup14() noexcept
        {
            return ins(compiler::EvmOpCode::DUP14);
        }

        EvmBuilder &dup15() noexcept
        {
            return ins(compiler::EvmOpCode::DUP15);
        }

        EvmBuilder &dup16() noexcept
        {
            return ins(compiler::EvmOpCode::DUP16);
        }

        EvmBuilder &swap1() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP1);
        }

        EvmBuilder &swap2() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP2);
        }

        EvmBuilder &swap3() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP3);
        }

        EvmBuilder &swap4() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP4);
        }

        EvmBuilder &swap5() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP5);
        }

        EvmBuilder &swap6() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP6);
        }

        EvmBuilder &swap7() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP7);
        }

        EvmBuilder &swap8() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP8);
        }

        EvmBuilder &swap9() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP9);
        }

        EvmBuilder &swap10() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP10);
        }

        EvmBuilder &swap11() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP11);
        }

        EvmBuilder &swap12() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP12);
        }

        EvmBuilder &swap13() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP13);
        }

        EvmBuilder &swap14() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP14);
        }

        EvmBuilder &swap15() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP15);
        }

        EvmBuilder &swap16() noexcept
        {
            return ins(compiler::EvmOpCode::SWAP16);
        }

        EvmBuilder &log1() noexcept
        {
            return ins(compiler::EvmOpCode::LOG1);
        }

        EvmBuilder &log2() noexcept
        {
            return ins(compiler::EvmOpCode::LOG2);
        }

        EvmBuilder &log3() noexcept
        {
            return ins(compiler::EvmOpCode::LOG3);
        }

        EvmBuilder &log4() noexcept
        {
            return ins(compiler::EvmOpCode::LOG4);
        }

        EvmBuilder &create() noexcept
        {
            return ins(compiler::EvmOpCode::CREATE);
        }

        EvmBuilder &call() noexcept
        {
            return ins(compiler::EvmOpCode::CALL);
        }

        EvmBuilder &callcode() noexcept
        {
            return ins(compiler::EvmOpCode::CALLCODE);
        }

        EvmBuilder &return_() noexcept
        {
            return ins(compiler::EvmOpCode::RETURN);
        }

        EvmBuilder &delegatecall() noexcept
        {
            return ins(compiler::EvmOpCode::DELEGATECALL);
        }

        EvmBuilder &create2() noexcept
        {
            return ins(compiler::EvmOpCode::CREATE2);
        }

        EvmBuilder &staticcall() noexcept
        {
            return ins(compiler::EvmOpCode::STATICCALL);
        }

        EvmBuilder &revert() noexcept
        {
            return ins(compiler::EvmOpCode::REVERT);
        }

        EvmBuilder &selfdestruct() noexcept
        {
            return ins(compiler::EvmOpCode::SELFDESTRUCT);
        }

    private:
        EvmBuilder &insert(instruction_type auto const &&inst) noexcept
        {
            ins_.push_back(inst);
            return *this;
        }

        size_t position() const
        {
            return ins_.size();
        }

        std::vector<Instruction::T> ins_{};
    };
}
