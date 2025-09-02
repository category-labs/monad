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

/**
 * parse an evm opcode text <file> and
 * write the resulting evm bytecode to <file>.evm
 *
 * -b switch reads in an evm bytecode file and
 *  writes the corresponding text to stdout
 *
 * see parser.hpp for details
 *
 */

#include <cstdint>
#include <cstdlib>
#include <format>
#include <ios>
#include <iostream>
#include <iterator>
#include <sstream>
#include <string>
#include <vector>

#include <CLI/CLI.hpp>

#include <evmc/evmc.h>

#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/utils/parser.hpp>

using namespace monad::vm::utils;
using namespace monad::vm::interpreter;

struct arguments
{
    bool verbose = false;
    bool binary = false;
    bool stdin = false;
    bool compile = false;
    bool validate = false;
    std::vector<std::string> filenames;
};

arguments parse_args(int const argc, char **const argv)
{
    auto app = CLI::App("evm opcode parser/printer");
    auto args = arguments{};

    app.add_option("filenames", args.filenames, "List of files to process")
        ->check(CLI::ExistingFile);

    app.add_flag(
        "-b,--binary",
        args.binary,
        "process input files as binary and show evm opcodes/data as text");

    app.add_flag("-c,--compile", args.compile, "compile the input files");
    app.add_option(
        "--validate",
        args.validate,
        std::format(
            "validate input files (default: {})"
            " - reports incorrect errors in some programs",
            args.validate));

    app.add_flag("-v,--verbose", args.verbose, "send debug info to stdout");

    app.add_flag(
        "-s,--stdin", args.stdin, "read from stdin and write to stdout");

    try {
        app.parse(argc, argv);
    }
    catch (CLI::ParseError const &e) {
        std::exit(app.exit(e));
    }

    return args;
}

std::vector<uint8_t> do_parse(
    parser_config const &config, std::string const &filename,
    std::string const &s, std::string const &outfile, std::ostream &os)
{
    if (config.verbose) {
        std::cerr << "parsing " << filename << '\n';
    }

    auto opcodes = parse_opcodes(config, s);
    if (config.verbose) {
        std::cerr << "writing " << outfile << '\n';
    }
    os.write(
        reinterpret_cast<char const *>(opcodes.data()),
        static_cast<long>(opcodes.size()));
    return opcodes;
}

void do_binary(
    parser_config const &config, std::string const &filename,
    std::vector<uint8_t> const &opcodes)
{
    if (config.verbose) {
        std::cerr << "printing " << filename << '\n';
    }

    std::cout << show_opcodes(opcodes) << '\n';
}

int main(int argc, char **argv)
{
    auto args = parse_args(argc, argv);

    parser_config const config{args.verbose, args.validate};

    if (args.stdin) {
        std::stringstream buffer;
        buffer << std::cin.rdbuf();
        std::string s = buffer.str();
        auto opcodes =
            args.binary ? std::vector<uint8_t>(s.begin(), s.end())
                        : do_parse(config, "<stdin>", s, "<stdout>", std::cout);

        if (args.binary) {
            do_binary(config, "<stdin>", opcodes);
        }
        MONAD_VM_ASSERT(opcodes.size() <= *code_size_t::max());
        if (args.compile) {
            auto rt = asmjit::JitRuntime{};
            monad::vm::compiler::native::compile<
                monad::EvmTraits<EVMC_LATEST_STABLE_REVISION>>(
                rt,
                opcodes.data(),
                code_size_t::unsafe_from(static_cast<uint32_t>(opcodes.size())),
                {.asm_log_path = "out.asm"});
        }
    }

    for (auto const &filename : args.filenames) {
        auto in = std::ifstream(filename, std::ios::binary);
        if (args.binary) {
            auto opcodes = std::vector<uint8_t>(
                std::istreambuf_iterator<char>(in),
                std::istreambuf_iterator<char>());
            do_binary(config, filename, opcodes);
        }
        else {
            auto s = std::string(
                std::istreambuf_iterator<char>(in),
                std::istreambuf_iterator<char>());
            auto outfile = filename + ".evm";
            auto os = std::ofstream(outfile, std::ios::binary);
            auto opcodes = do_parse(config, filename, s, outfile, os);
            if (args.compile) {
                auto outfile_asm = filename + ".asm";
                auto rt = asmjit::JitRuntime{};
                monad::vm::compiler::native::compile<
                    monad::EvmTraits<EVMC_LATEST_STABLE_REVISION>>(
                    rt,
                    opcodes.data(),
                    code_size_t::unsafe_from(
                        static_cast<uint32_t>(opcodes.size())),
                    {.asm_log_path = outfile_asm.c_str()});
            }
        }
    }
    return 0;
}
