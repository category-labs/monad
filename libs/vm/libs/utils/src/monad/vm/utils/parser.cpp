#include <monad/vm/core/assert.h>
#include <monad/vm/core/cases.hpp>
#include <monad/vm/evm/opcodes.hpp>
#include <monad/vm/runtime/uint256.hpp>
#include <monad/vm/utils/evm-as.hpp>
#include <monad/vm/utils/evm-as/builder.hpp>
#include <monad/vm/utils/evm-as/compiler.hpp>
#include <monad/vm/utils/evm-as/validator.hpp>
#include <monad/vm/utils/parser.hpp>

#include <CLI/CLI.hpp>

#include <evmc/evmc.h>

#include <algorithm>
#include <array>
#include <cassert>
#include <cctype>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <iostream>
#include <iterator>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
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
                if (isxdigit(*input)) {
                    do {
                        input++;
                    }
                    while (isxdigit(*input));
                    return input;
                }
            }
        }
        return input0;
    }

    char const *try_parse_decimal_constant(char const *input)
    {
        while (isdigit(*input)) {
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
            while (isalnum(*input));
        }
        return input;
    }

    char const *drop_spaces(char const *input)
    {
        while (*input == ' ') {
            input++;
        }
        return input;
    }

    void err(std::string_view msg, std::string_view value)
    {
        std::cerr << "error: " << msg << ": " << value << '\n';
        exit(1);
    }

    void err(evm_as::ValidationError const &err)
    {
        std::cerr << "error: " << err.msg << std::endl;
    }

    std::pair<char const *, std::variant<runtime::uint256_t, std::string>>
    parse_constant_or_label(char const *input)
    {
        input = drop_spaces(input);
        auto const *p = try_parse_hex_constant(input);
        if (p != input) {
            auto s = std::string(input, p);
            return std::make_pair(p, runtime::uint256_t::from_string(s));
        }

        p = try_parse_decimal_constant(input);
        if (p != input) {
            auto s = std::string(input, p);
            return std::make_pair(p, runtime::uint256_t::from_string(s));
        }
        p = try_parse_label(input);
        if (p == input) {
            err("missing argument to push", "");
        }

        auto s = std::string(input, p);
        return std::make_pair(p, s);
    }

    char const *try_parse_opname(char const *input)
    {
        if (isalpha(*input)) {
            do {
                input++;
            }
            while (isalnum(*input));
        }
        return input;
    }

    bool is_push_with_arg(std::string_view op)
    {
        return (
            find(push_ops_with_arg.begin(), push_ops_with_arg.end(), op) !=
            push_ops_with_arg.end());
    }

    void warn(std::string_view msg, std::string_view value)
    {
        std::cerr << "warning: " << msg << ": " << value << '\n';
    }

    std::optional<uint8_t> find_opcode(std::string_view op)
    {
        auto const &tbl = monad::vm::compiler::make_opcode_table<
            EVMC_LATEST_STABLE_REVISION>();
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
            EVMC_LATEST_STABLE_REVISION>();
        for (std::size_t i = 0; i < opcodes.size(); ++i) {
            auto c = opcodes[i];
            ss << std::format("[{:#x}] {:#x} {}\n", i, c, tbl[opcodes[i]].name);
            if (c >= PUSH1 && c <= PUSH32) {
                for (auto j = 0; j < c - PUSH0; ++j) {
                    i++;
                    ss << std::format("[{:#x}] {:#x}\n", i, opcodes[i]);
                }
            }
        }
        return ss.str();
    }

    std::vector<uint8_t> compile_tokens(
        parser_config const &config,
        evm_as::EvmBuilder<EVMC_LATEST_STABLE_REVISION> const &eb)
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
            exit(1);
        }

        evm_as::compile(eb, opcodes);

        if (config.verbose) {
            std::cerr << "// done\n";
            show_opcodes(opcodes);
        }

        return opcodes;
    }

    std::vector<uint8_t>
    parse_opcodes_helper(parser_config const &config, std::string const &str)
    {
        auto eb = evm_as::latest();
        char const *input = str.c_str();

        while (*input) {
            auto const *p = try_parse_hex_constant(input);
            if (p != input) {
                warn("unexpected hex constant", std::string_view(input, p));
                input = p;
                continue;
            }

            p = try_parse_decimal_constant(input);
            if (p != input) {
                warn("unexpected decimal constant", std::string_view(input, p));
                input = p;
                continue;
            }

            p = try_parse_label(input);
            if (p != input) {
                warn("unexpected label", std::string_view(input, p));
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
                std::transform(op.begin(), op.end(), op.begin(), ::toupper);
                input = p;
                if (op == "PUSH0") {
                    eb.push0();
                }
                else if (is_push_with_arg(op)) {
                    auto r = parse_constant_or_label(input);
                    input = r.first;

                    std::visit(
                        Cases{
                            [&](runtime::uint256_t const &imm) -> void {
                                auto const *const pushops =
                                    push_ops_with_arg.data();
                                auto d = std::distance(
                                    pushops,
                                    std::find(pushops, pushops + 33, op));
                                MONAD_VM_ASSERT(d >= 0);
                                size_t const n = static_cast<size_t>(d);
                                if (n == 0) {
                                    eb.push0();
                                }
                                else {
                                    eb.push(n, imm);
                                }
                            },
                            [&](std::string const &label) -> void {
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
                        eb.jumpdest(std::string(input, p));
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

            input++; // otherwise ignore
        }
        return compile_tokens(config, eb);
    }

    std::vector<uint8_t>
    parse_opcodes(parser_config const &config, std::string const &str)
    {
        return parse_opcodes_helper(config, str);
    }
}
