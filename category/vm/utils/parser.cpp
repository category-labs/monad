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

#include <category/core/assert.h>
#include <category/core/cases.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/evm-as/utils.hpp>
#include <category/vm/utils/evm-as/validator.hpp>
#include <category/vm/utils/parser.hpp>

#include <algorithm>
#include <array>
#include <cassert>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <format>
#include <iostream>
#include <iterator>
#include <optional>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <variant>
#include <vector>

using namespace monad::vm::compiler;

namespace monad::vm::utils
{
    constexpr auto push_ops_with_arg = std::array{
        "PUSH", // generic push
        "PUSH1",  "PUSH2",  "PUSH3",  "PUSH4",  "PUSH5",  "PUSH6",  "PUSH7",
        "PUSH8",  "PUSH9",  "PUSH10", "PUSH11", "PUSH12", "PUSH13", "PUSH14",
        "PUSH15", "PUSH16", "PUSH17", "PUSH18", "PUSH19", "PUSH20", "PUSH21",
        "PUSH22", "PUSH23", "PUSH24", "PUSH25", "PUSH26", "PUSH27", "PUSH28",
        "PUSH29", "PUSH30", "PUSH31", "PUSH32",
    };

    char const *try_parse_line_comment(char const *input)
    {
        if (*input == '/') {
            do {
                input++;
            }
            while (*input && *input != '\n');
        }
        return input;
    }

    char const *try_parse_hex_constant(char const *input)
    {
        auto const *input0 = input;

        if (*input == '0') {
            input++;
            if (*input == 'x' || *input == 'X') {
                input++;
                if (isxdigit(static_cast<unsigned char>(*input))) {
                    do {
                        input++;
                    }
                    while (isxdigit(static_cast<unsigned char>(*input)));
                    return input;
                }
            }
        }
        return input0;
    }

    char const *try_parse_decimal_constant(char const *input)
    {
        while (isdigit(static_cast<unsigned char>(*input))) {
            input++;
        }
        return input;
    }

    char const *try_parse_label(char const *input)
    {
        if (*input == '.') {
            do {
                input++;
            }
            while (isalnum(static_cast<unsigned char>(*input)) ||
                   *input == '_');
        }
        return input;
    }

    char const *drop_spaces(char const *input)
    {
        while (*input == ' ' || *input == '\t' || *input == '\r') {
            input++;
        }
        return input;
    }

    [[noreturn]] void
    err(std::string_view const msg, std::string_view const value)
    {
        throw std::invalid_argument(std::format("{}: {}", msg, value));
    }

    void err(evm_as::ValidationError const &err)
    {
        std::cerr << "error: " << err.msg << std::endl;
    }

    std::pair<char const *, std::variant<uint256_t, std::string>>
    parse_constant_or_label(char const *input)
    {
        input = drop_spaces(input);
        auto const *p = try_parse_hex_constant(input);
        if (p != input) {
            auto const s = std::string(input, p);
            return std::make_pair(p, uint256_t::from_string(s));
        }

        p = try_parse_decimal_constant(input);
        if (p != input) {
            auto const s = std::string(input, p);
            return std::make_pair(p, uint256_t::from_string(s));
        }
        p = try_parse_label(input);
        if (p == input) {
            err("missing argument to push", "");
        }

        auto const s = std::string(input, p);
        return std::make_pair(p, s);
    }

    char const *try_parse_opname(char const *input)
    {
        if (isalpha(static_cast<unsigned char>(*input))) {
            do {
                input++;
            }
            while (isalnum(static_cast<unsigned char>(*input)));
        }
        return input;
    }

    bool is_push_with_arg(std::string_view const op)
    {
        return (
            find(push_ops_with_arg.begin(), push_ops_with_arg.end(), op) !=
            push_ops_with_arg.end());
    }

    void warn(
        parser_config const &config, std::string_view const msg,
        std::string_view const value)
    {
        if (config.strict) {
            err(msg, value);
        }
        std::cerr << "warning: " << msg << ": " << value << '\n';
    }

    std::optional<uint8_t> find_opcode(std::string_view const op)
    {
        auto const &tbl = monad::vm::compiler::make_opcode_table<
            EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>>();
        size_t i;
        for (i = 0; i < tbl.size(); ++i) {
            if (tbl[i].name == op) {
                break;
            }
        }
        if (i < tbl.size()) {
            return static_cast<uint8_t>(i);
        }
        return std::nullopt;
    }

    std::string show_opcodes(std::vector<uint8_t> const &opcodes)
    {
        std::stringstream ss;
        auto const &tbl = monad::vm::compiler::make_opcode_table<
            EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>>();
        for (size_t i = 0; i < opcodes.size(); ++i) {
            auto c = opcodes[i];
            ss << std::format("[{:#x}] {:#x} {}\n", i, c, tbl[opcodes[i]].name);
            if (is_push_opcode(c)) {
                // A trailing push may have a truncated immediate region.
                size_t const n = get_push_opcode_index(c);
                size_t const avail = std::min(n, opcodes.size() - i - 1);
                for (size_t j = 0; j < avail; ++j) {
                    i++;
                    ss << std::format("[{:#x}] {:#x}\n", i, opcodes[i]);
                }
                if (avail < n) {
                    ss << std::format(
                        "// truncated PUSH{}: {} of {} immediate bytes "
                        "missing (zero-padded when executed)\n",
                        n,
                        n - avail,
                        n);
                }
            }
        }
        return ss.str();
    }

    std::vector<uint8_t> compile_tokens(
        parser_config const &config,
        evm_as::EvmBuilder<EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>> const
            &eb)
    {
        std::vector<uint8_t> opcodes{};
        std::vector<evm_as::ValidationError> errors{};
        if (config.verbose) {
            std::cerr << "// validating and compiling\n";
        }
        if (config.validate && !evm_as::validate(eb, errors)) {
            // Print at most 5 validation errors, and then exit.
            for (size_t i = 0; i < std::min(errors.size(), size_t{5}); i++) {
                err(errors[i]);
            }
            throw std::invalid_argument("Program validation failed");
        }

        evm_as::compile(eb, opcodes);

        if (config.verbose) {
            std::cerr << "// done\n";
            std::cerr << show_opcodes(opcodes);
        }

        return opcodes;
    }

    std::vector<uint8_t> parse_opcodes_helper(
        parser_config const &config, std::string const &str,
        std::vector<uint32_t> *source_lines)
    {
        auto eb = evm_as::latest();
        char const *input = str.c_str();
        uint32_t line = 1;
        std::vector<uint32_t> instruction_lines;
        std::unordered_set<std::string> labels;
        std::vector<std::pair<std::string, uint32_t>> references;
        if (config.strict && str.find('\0') != std::string::npos) {
            err("Unexpected NUL character", "");
        }

        try {
            while (*input) {
                if (std::isspace(static_cast<unsigned char>(*input))) {
                    if (*input == '\n') {
                        ++line;
                    }
                    ++input;
                    continue;
                }
                if (config.strict && *input == '/' && input[1] != '/') {
                    err("Expected // comment", "/");
                }
                auto const *p = try_parse_hex_constant(input);
                if (p != input) {
                    warn(
                        config,
                        "unexpected hex constant",
                        std::string_view(input, p));
                    input = p;
                    continue;
                }

                p = try_parse_decimal_constant(input);
                if (p != input) {
                    warn(
                        config,
                        "unexpected decimal constant",
                        std::string_view(input, p));
                    input = p;
                    continue;
                }

                p = try_parse_label(input);
                if (p != input) {
                    warn(
                        config, "unexpected label", std::string_view(input, p));
                    input = p;
                    continue;
                }

                p = try_parse_line_comment(input);
                if (p != input) {
                    input = p;
                    continue;
                }

                p = try_parse_opname(input);
                if (p != input) {
                    auto op = std::string(input, p);
                    std::ranges::transform(op, op.begin(), [](unsigned char c) {
                        return static_cast<char>(std::toupper(c));
                    });
                    if (source_lines) {
                        instruction_lines.push_back(line);
                    }
                    input = p;
                    if (op == "PUSH0") {
                        eb.push0();
                    }
                    else if (is_push_with_arg(op)) {
                        auto r = parse_constant_or_label(input);
                        input = r.first;

                        std::visit(
                            Cases{
                                [&](uint256_t const &imm) -> void {
                                    auto const *const pushops =
                                        push_ops_with_arg.data();
                                    auto const d = std::distance(
                                        pushops,
                                        std::find(pushops, pushops + 33, op));
                                    MONAD_ASSERT(d >= 0);
                                    size_t const n = static_cast<size_t>(d);
                                    if (n == 0) {
                                        eb.push(imm);
                                    }
                                    else {
                                        if (config.strict &&
                                            evm_as::byte_width(imm) > n) {
                                            err("Immediate does not fit " + op,
                                                imm.to_string(16));
                                        }
                                        eb.push(n, imm);
                                    }
                                },
                                [&](std::string const &label) -> void {
                                    if (config.strict && label.size() == 1) {
                                        err("Expected a label name after .",
                                            label);
                                    }
                                    if (config.strict) {
                                        references.emplace_back(label, line);
                                    }
                                    eb.push(label);
                                }},
                            r.second);
                    }
                    else if (op == "JUMPDEST") {
                        input = drop_spaces(input);
                        p = try_parse_label(input);
                        if (p == input) {
                            eb.jumpdest();
                        }
                        else {
                            auto const label = std::string(input, p);
                            if (config.strict &&
                                (label.size() == 1 ||
                                 !labels.insert(label).second)) {
                                err("Invalid or duplicate label", label);
                            }
                            eb.jumpdest(label);
                            input = p;
                        }
                    }
                    else {
                        std::optional<uint8_t> opcode = find_opcode(op);
                        if (!opcode.has_value()) {
                            err("unknown opcode", op);
                        }
                        else {
                            eb.ins(static_cast<monad::vm::compiler::EvmOpCode>(
                                opcode.value()));
                        }
                    }

                    continue;
                }

                if (config.strict) {
                    err("Unexpected character", std::string_view(input, 1));
                }
                input++; // otherwise ignore
            }
            if (config.strict) {
                for (auto const &[label, reference_line] : references) {
                    if (!labels.contains(label)) {
                        line = reference_line;
                        err("Undefined label", label);
                    }
                }
            }
            auto code = compile_tokens(config, eb);
            if (source_lines) {
                source_lines->assign(code.size(), 0);
                size_t offset = 0;
                for (auto const source_line : instruction_lines) {
                    auto const opcode = code.at(offset);
                    auto const size = 1 + (is_push_opcode(opcode)
                                               ? get_push_opcode_index(opcode)
                                               : 0);
                    std::fill_n(
                        source_lines->begin() +
                            static_cast<std::ptrdiff_t>(offset),
                        size,
                        source_line);
                    offset += size;
                }
            }
            return code;
        }
        catch (std::exception const &error) {
            throw std::invalid_argument(
                std::format("Line {}: {}", line, error.what()));
        }
    }

    std::vector<uint8_t> parse_opcodes(
        parser_config const &config, std::string const &str,
        std::vector<uint32_t> *source_lines)
    {
        try {
            return parse_opcodes_helper(config, str, source_lines);
        }
        catch (std::exception const &error) {
            if (config.strict) {
                throw;
            }
            std::cerr << "error: " << error.what() << '\n';
            std::exit(1);
        }
    }
}
