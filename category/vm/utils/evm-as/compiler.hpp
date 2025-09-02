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
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/instruction.hpp>
#include <category/vm/utils/evm-as/resolver.hpp>
#include <category/vm/utils/evm-as/utils.hpp>

#include <evmc/evmc.h>

#include <concepts>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <variant>
#include <vector>

namespace monad::vm::utils::evm_as::internal
{
    using namespace monad::vm::utils::evm_as;

    struct annot_context
    {
        std::vector<std::string> vstack{};
        size_t next_subscript = 0;
        size_t next_letter = 0;
    };

    void emit_annotation(
        annot_context &ctx, size_t prefix_len, size_t desired_offset,
        std::ostream &os);

    std::string new_var(annot_context &ctx);

    static inline bool
    simulate_binop(annot_context &ctx, std::string_view const &binop)
    {
        auto const elem_a = ctx.vstack.back();
        ctx.vstack.pop_back();
        auto const elem_b = ctx.vstack.back();
        ctx.vstack.pop_back();
        ctx.vstack.push_back(std::format("({} {} {})", elem_a, binop, elem_b));
        return true;
    }

    template <Traits traits>
    bool simulate_stack_effect(Instruction::T inst, annot_context &ctx)
    {
        return std::visit(
            Cases{
                [&](PlainI const &plain) -> bool {
                    auto const &info =
                        compiler::opcode_table<traits>[plain.opcode];
                    if (info.min_stack > ctx.vstack.size()) {
                        // Stack underflow
                        return false;
                    }

                    if (compiler::EvmOpCode::DUP1 <= plain.opcode &&
                        plain.opcode <= compiler::EvmOpCode::DUP16) {
                        auto const n =
                            static_cast<size_t>(
                                plain.opcode - compiler::EvmOpCode::DUP1) +
                            1;
                        auto const elem = ctx.vstack[ctx.vstack.size() - n];
                        ctx.vstack.push_back(elem);
                        return true;
                    }

                    if (compiler::EvmOpCode::SWAP1 <= plain.opcode &&
                        plain.opcode <= compiler::EvmOpCode::SWAP16) {
                        auto const n =
                            static_cast<size_t>(
                                plain.opcode - compiler::EvmOpCode::SWAP1) +
                            1;
                        std::swap(
                            ctx.vstack[ctx.vstack.size() - 1],
                            ctx.vstack[ctx.vstack.size() - 1 - n]);
                        return true;
                    }

                    switch (plain.opcode) {
                    case compiler::EvmOpCode::ADD:
                        return simulate_binop(ctx, "+");
                    case compiler::EvmOpCode::SUB:
                        return simulate_binop(ctx, "-");
                    case compiler::EvmOpCode::MUL:
                        return simulate_binop(ctx, "*");
                    case compiler::EvmOpCode::DIV:
                    case compiler::EvmOpCode::SDIV:
                        return simulate_binop(ctx, "/");
                    case compiler::EvmOpCode::MOD:
                    case compiler::EvmOpCode::SMOD:
                        return simulate_binop(ctx, "%");
                    case compiler::EvmOpCode::EXP:
                        return simulate_binop(ctx, "^");
                    case compiler::EvmOpCode::XOR:
                        return simulate_binop(ctx, "xor");
                    default:
                        break;
                    }

                    // Default case
                    for (size_t i = 0; i < info.min_stack; i++) {
                        ctx.vstack.pop_back();
                    }

                    if (info.stack_increase > 0) {
                        if (plain.opcode == compiler::EvmOpCode::PUSH0) {
                            ctx.vstack.push_back("0");
                        }
                        else {
                            for (size_t i = 0; i < info.stack_increase; i++) {
                                ctx.vstack.push_back(new_var(ctx));
                            }
                        }
                    }
                    return info.min_stack > 0 || info.stack_increase > 0;
                },
                [&](PushI const &push) -> bool {
                    if (push.imm > std::numeric_limits<uint32_t>::max()) {
                        ctx.vstack.push_back(new_var(ctx));
                    }
                    else {
                        ctx.vstack.push_back(push.imm.to_string(10));
                    }
                    return true;
                },
                [&](PushLabelI const &push) -> bool {
                    ctx.vstack.push_back(push.label);
                    return true;
                },
                [](auto const &) -> bool { return false; }},
            inst);
    }
}

namespace monad::vm::utils::evm_as
{
    namespace mc = monad::vm::compiler;

    //
    // Generic bytecode compiler
    //
    template <Traits traits>
    void compile(
        EvmBuilder<traits> const &eb,
        std::invocable<uint8_t const> auto emit_byte)
    {
        auto const label_offsets = resolve_labels<traits>(eb);
        for (auto const &ins : eb) {
            std::array<uint8_t, sizeof(runtime::uint256_t)> imm_bytes{};
            if (Instruction::is_comment(ins)) {
                continue;
            }
            std::visit(
                Cases{
                    [&](PlainI const &plain) -> void {
                        emit_byte(plain.opcode);
                    },
                    [&](PushI const &push) -> void {
                        emit_byte(push.opcode);
                        // SAFETY: The buffer `imm_bytes` is
                        // large enough to hold an uint256_t.
                        push.imm.store_be(imm_bytes.data());
                        auto const n = push.n();
                        for (size_t i = 0; i < n; i++) {
                            emit_byte(imm_bytes[32 - n + i]);
                        }
                    },
                    [&](PushLabelI const &push) -> void {
                        auto const it = label_offsets.find(push.label);
                        if (it == label_offsets.end()) {
                            // Undefined label
                            emit_byte(0xFE);
                            return;
                        }

                        size_t const offset = it->second;
                        size_t const n =
                            offset == 0 ? offset : byte_width(offset);
                        emit_byte(
                            mc::EvmOpCode::PUSH0 + static_cast<uint8_t>(n));
                        // Note: assumes we are executing on a
                        // little endian machine.
                        for (size_t i = 0; i < n; i++) {
                            emit_byte((offset >> ((n - i - 1) * 8)) & 0xFF);
                        }
                    },
                    [&](JumpdestI const &) -> void {
                        emit_byte(mc::EvmOpCode::JUMPDEST);
                    },
                    [&](InvalidI const &) -> void { emit_byte(0xFE); },
                    [&](auto const &) -> void { MONAD_VM_ASSERT(false); }},
                ins);
        }
    }

    // Assembles and emits the corresponding byte code of the provided
    // builder object to the provided `bytecode` vector.
    template <Traits traits>
    inline void
    compile(EvmBuilder<traits> const &eb, std::vector<uint8_t> &bytecode)
    {
        bytecode.reserve(eb.size() /* optimistic estimate */);
        compile<traits>(
            eb, [&](uint8_t const byte) -> void { bytecode.push_back(byte); });
    }

    // Assembles and emits the corresponding byte code of the provided
    // builder object to the provided `os` out stream.
    template <Traits traits>
    inline void compile(EvmBuilder<traits> const &eb, std::ostream &os)
    {
        compile<traits>(eb, [&](uint8_t const byte) -> void {
            os << static_cast<std::ostream::char_type>(byte);
        });
    }

    // Assembles and emits the corresponding byte code of the provided
    // builder object in the returned string.
    template <Traits traits>
    inline std::string compile(EvmBuilder<traits> const &eb)
    {
        std::stringstream ss{};
        compile<traits>(eb, ss);
        return ss.str();
    }

    // Mnemonic compiler config
    struct mnemonic_config
    {
        constexpr mnemonic_config()
            : resolve_labels(false)
            , annotate(false)
            , desired_annotation_offset(32)
        {
        }

        constexpr mnemonic_config(
            bool resolve_labels, bool annotate, size_t offset)
            : resolve_labels(resolve_labels)
            , annotate(annotate)
            , desired_annotation_offset(offset)
        {
        }

        bool resolve_labels;
        bool annotate;
        size_t desired_annotation_offset;
    };

    //
    // Mnemonic compiler
    //
    template <Traits traits>
    inline void mcompile(
        EvmBuilder<traits> const &eb, std::ostream &os,
        mnemonic_config config = mnemonic_config())
    {
        auto const label_offsets =
            [&]() -> std::unordered_map<std::string, size_t> {
            if (config.resolve_labels) {
                return resolve_labels<traits>(eb);
            }
            return {};
        }();
        internal::annot_context ctx{{}, 0};
        for (auto const &ins : eb) {
            size_t length = std::visit(
                Cases{
                    [&](PlainI const &plain) -> size_t {
                        auto const info =
                            mc::opcode_table<traits>[plain.opcode];
                        os << info.name;
                        return info.name.size();
                    },
                    [&](PushI const &push) -> size_t {
                        auto const info = mc::opcode_table<traits>[push.opcode];
                        std::string imm_str = push.imm.to_string(16);
                        std::transform(
                            imm_str.begin(),
                            imm_str.end(),
                            imm_str.begin(),
                            ::toupper);

                        os << info.name << " 0x" << imm_str;
                        return info.name.size() + 3 + imm_str.size();
                    },
                    [&](PushLabelI const &push) -> size_t {
                        if (config.resolve_labels) {
                            auto const it = label_offsets.find(push.label);
                            if (it == label_offsets.end()) {
                                // Undefined label
                                os << "INVALID";
                                return 7;
                            }
                            size_t offset = it->second;
                            size_t n =
                                offset == 0 ? offset : byte_width(offset);
                            std::string const str =
                                std::format("PUSH{} 0x{:X}", n, offset);
                            os << str;
                            return str.size();
                        }
                        else {
                            os << "PUSH " << push.label;
                            return 5 + push.label.size();
                        }
                    },
                    [&](JumpdestI const &jumpdest) -> size_t {
                        os << "JUMPDEST";
                        if (!config.resolve_labels) {
                            os << ' ' << jumpdest.label;
                            return 9 + jumpdest.label.size();
                        }
                        return 8;
                    },
                    [&](InvalidI const &) -> size_t {
                        os << "INVALID";
                        return 7;
                    },
                    [&](CommentI const &comment) -> size_t {
                        if (comment.msg.empty()) {
                            os << "//";
                            return 0;
                        }
                        std::stringstream ss(comment.msg);
                        std::string msg;
                        bool first = true;
                        while (std::getline(ss, msg, '\n')) {
                            if (!first) {
                                os << std::endl;
                            }
                            os << "// " << msg;
                            first = false;
                        }
                        return 0;
                    }},
                ins);
            if (config.annotate && length > 0) {
                if (internal::simulate_stack_effect<traits>(ins, ctx)) {
                    internal::emit_annotation(
                        ctx, length, config.desired_annotation_offset, os);
                }
            }
            os << std::endl;
        }
    }

    // Returns a mnemonic representation of the provided builder object
    // as a string; convenient for testing.
    template <Traits traits>
    inline std::string mcompile(
        EvmBuilder<traits> const &eb,
        mnemonic_config config = mnemonic_config())
    {
        std::stringstream ss{};
        mcompile(eb, ss, config);
        return ss.str();
    }
}
