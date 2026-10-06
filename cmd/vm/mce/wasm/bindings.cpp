// Copyright (C) 2026 Category Labs, Inc.
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

#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/evm/revision.h>
#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/intercode.hpp>
#include <category/vm/utils/load_program.hpp>
#include <category/vm/utils/parser.hpp>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <exception>
#include <iostream>
#include <iterator>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef __EMSCRIPTEN__
    #include <emscripten/bind.h>
    #include <emscripten/val.h>
#endif

namespace
{
    struct CompileResult
    {
        std::string assembly;
        std::string error;
    };

    struct AssembleResult
    {
        std::string bytecode;
        std::vector<uint32_t> source_lines;
        std::string error;
    };

    AssembleResult assemble_mnemonic(std::string const &source)
    {
        try {
            if (source.size() > 4 * 1024 * 1024) {
                throw std::invalid_argument("Source exceeds 4 MiB");
            }
            AssembleResult result;
            auto const code = monad::vm::utils::parse_opcodes(
                {false, false, true}, source, &result.source_lines);
            if (code.size() >= (1U << 20)) {
                throw std::invalid_argument(
                    "Bytecode must be smaller than 1 MiB");
            }
            constexpr char hex[] = "0123456789abcdef";
            result.bytecode.reserve(code.size() * 2);
            for (auto const byte : code) {
                result.bytecode.push_back(hex[byte >> 4]);
                result.bytecode.push_back(hex[byte & 0xf]);
            }
            return result;
        }
        catch (std::exception const &error) {
            return {{}, {}, error.what()};
        }
    }

    template <monad::Traits traits>
    std::string compile(std::vector<uint8_t> const &code)
    {
        using namespace monad::vm;
        auto const ir = compiler::basic_blocks::make_ir<traits>(
            code.data(),
            interpreter::code_size_t::unsafe_from(
                static_cast<uint32_t>(code.size())));
        return compiler::native::compile_assembly<traits>(ir);
    }

    CompileResult compile_hex(std::string source, std::string revision)
    {
        try {
            // Bound both preprocessing and compilation work for browser inputs.
            if (source.size() > 4 * 1024 * 1024) {
                throw std::invalid_argument("Source exceeds 4 MiB");
            }
            std::erase_if(
                source, [](unsigned char c) { return std::isspace(c); });
            if (source.starts_with("0x") || source.starts_with("0X")) {
                source.erase(0, 2);
            }
            if (source.size() % 2 != 0) {
                throw std::invalid_argument("Expected complete hex byte pairs");
            }
            if (source.size() / 2 >= (1U << 20)) {
                throw std::invalid_argument(
                    "Bytecode must be smaller than 1 MiB");
            }
            auto const code = monad::vm::utils::parse_hex_program(source);
            std::ranges::transform(
                revision, revision.begin(), [](unsigned char c) {
                    return static_cast<char>(std::toupper(c));
                });
#define EVM_REVISION(name)                                                     \
    if (revision == #name) {                                                   \
        return {compile<monad::EvmTraits<MONAD_ETH_##name>>(code), {}};        \
    }
            EVM_REVISION(BERLIN)
            EVM_REVISION(LONDON)
            EVM_REVISION(PARIS)
            EVM_REVISION(SHANGHAI)
            EVM_REVISION(CANCUN)
            EVM_REVISION(PRAGUE)
            EVM_REVISION(OSAKA)
            EVM_REVISION(AMSTERDAM)
#undef EVM_REVISION
            if (revision == "LATEST") {
                return {
                    compile<monad::EvmTraits<MONAD_ETH_LATEST_STABLE_REVISION>>(
                        code),
                    {}};
            }
#define MONAD_REVISION(name)                                                   \
    if (revision == "MONAD_" #name) {                                          \
        return {compile<monad::MonadTraits<MONAD_##name>>(code), {}};          \
    }
            MONAD_REVISION(ZERO)
            MONAD_REVISION(ONE)
            MONAD_REVISION(TWO)
            MONAD_REVISION(THREE)
            MONAD_REVISION(FOUR)
            MONAD_REVISION(FIVE)
            MONAD_REVISION(SIX)
            MONAD_REVISION(SEVEN)
            MONAD_REVISION(EIGHT)
            MONAD_REVISION(NINE)
            MONAD_REVISION(TEN)
            MONAD_REVISION(NEXT)
#undef MONAD_REVISION
            throw std::invalid_argument("Unsupported revision: " + revision);
        }
        catch (monad::vm::compiler::native::Nativecode::
                   SizeEstimateOutOfBounds const &) {
            return {{}, "Generated code exceeds the compiler size limit"};
        }
        catch (std::exception const &error) {
            return {{}, error.what()};
        }
    }
}

#ifdef __EMSCRIPTEN__
EMSCRIPTEN_BINDINGS(mce)
{
    emscripten::value_object<CompileResult>("CompileResult")
        .field("assembly", &CompileResult::assembly)
        .field("error", &CompileResult::error);
    emscripten::function("compileHex", &compile_hex);
    emscripten::function(
        "assembleMnemonic", +[](std::string const &source) {
            auto const result = assemble_mnemonic(source);
            auto value = emscripten::val::object();
            value.set("bytecode", result.bytecode);
            value.set(
                "sourceLines", emscripten::val::array(result.source_lines));
            value.set("error", result.error);
            return value;
        });
}
#else
// Native reference executable for checking assembly parity with WASM.
int main(int argc, char **argv)
{
    std::string source = argc > 2
                             ? argv[2]
                             : std::string{
                                   std::istreambuf_iterator<char>{std::cin},
                                   std::istreambuf_iterator<char>{}};
    if (argc > 3) {
        auto const result = assemble_mnemonic(source);
        if (!result.error.empty()) {
            std::cerr << result.error << '\n';
            return 1;
        }
        source = result.bytecode;
        if (std::string{argv[3]} == "--bytecode") {
            std::cout << source << '\n';
            return 0;
        }
    }
    auto const result = compile_hex(source, argc > 1 ? argv[1] : "latest");
    if (!result.error.empty()) {
        std::cerr << result.error << '\n';
        return 1;
    }
    std::cout << result.assembly;
}
#endif
