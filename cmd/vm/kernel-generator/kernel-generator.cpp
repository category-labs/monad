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

#include <category/vm/evm/opcodes.hpp>
#include <category/vm/runtime/uint256.hpp>
#include <category/vm/utils/evm-as.hpp>
#include <category/vm/utils/evm-as/builder.hpp>
#include <category/vm/utils/evm-as/compiler.hpp>
#include <category/vm/utils/evm-as/validator.hpp>

#include <test_resource_data.h>

#include "evmc/helpers.h"
#include <CLI/CLI.hpp>
#include <evmc/evmc.h>

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <format>
#include <fstream>
#include <functional>
#include <ios>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

struct arguments
{
    bool opaque_parameters = true;
    bool epilogue = false;
};

struct emitter_config
{
    bool validate;
    monad::vm::utils::evm_as::mnemonic_config mconfig;
};

static arguments parse_args(int const argc, char **const argv)
{
    auto app = CLI::App("Computational micro kernel generator");
    auto args = arguments{};

    app.add_option(
        "--opaque-parameters",
        args.opaque_parameters,
        std::format(
            "Hide the concrete parameters from the optimizer (default: {})",
            args.opaque_parameters));
    app.add_option(
        "--with-epilogue",
        args.epilogue,
        std::format(
            "Kernels return their respective results (default: {})",
            args.epilogue));

    try {
        app.parse(argc, argv);
    }
    catch (CLI::ParseError const &e) {
        std::exit(app.exit(e));
    }

    return args;
}

namespace fs = std::filesystem;
using namespace monad::vm::utils;
using namespace monad::vm::runtime;
using EvmBuilder = evm_as::EvmBuilder<EVMC_LATEST_STABLE_REVISION>;

namespace monad::vm::utils::evm_as::kernels
{

    struct KernelBuilder : public ::EvmBuilder
    {
        KernelBuilder &loop(
            uint32_t niterations, size_t in, size_t out,
            ::EvmBuilder const &body)
        {
            if (in > 15) {
                throw std::invalid_argument("input stack is too large");
            }
            int64_t const N = -1 * static_cast<int64_t>(niterations);
            comment("Loop iterator initialization").spush(N);
            if (in > 0) {
                for (size_t i = in; i > 0; i--) {
                    swap(i);
                }
            }

            comment("Computational kernel start")
                .jumpdest("LOOP")
                .append(body)
                .comment("Increment iterator");
            if (out > 0) {
                swap(out);
            }

            push(1).add().dup1();
            if (out > 0) {
                swap(out + 1).swap1();
            }

            jumpi("LOOP").comment("Computational kernel end");

            return *this;
        }

        KernelBuilder &prepare_binop_arguments(
            size_t nclones, runtime::uint256_t const &a,
            runtime::uint256_t const &b, bool opaque_parameters)
        {
            comment(std::format("    Setup arguments: {}", nclones + 1));
            if (opaque_parameters) {
                comment("    Opaque parameters: hide the concrete values from "
                        "the optimizer")
                    .opacify(b)
                    .opacify(a);
            }
            else {
                push(b).push(a);
            }

            for (size_t i = 0; i < nclones; i++) {
                comment(std::format("{:4}Arguments clone #{}", "", i + 1))
                    .dup2()
                    .dup2();
            }

            return *this;
        }

        KernelBuilder &binop_loop_body(compiler::EvmOpCode binop)
        {
            ins(binop)
                .swap8()
                .swap1()
                .ins(binop)
                .swap6()
                .ins(binop)
                .swap4()
                .swap1()
                .ins(binop)
                .swap2()
                .ins(binop)
                .dup1()
                .dup3()
                .dup5()
                .dup7()
                .dup9();
            return *this;
        }

        KernelBuilder &epilogue()
        {
            comment("=== Epilogue").push0().mstore().push(32).push0().return_();

            return *this;
        }

        KernelBuilder &comment(std::string const &msg)
        {
            return static_cast<KernelBuilder &>(EvmBuilder::comment(msg));
        }

        KernelBuilder &
        opacify(std::variant<runtime::uint256_t, std::string> arg)
        {
            push0();
            std::visit(
                Cases{
                    [&](runtime::uint256_t const &imm) -> void { push(imm); },
                    [&](std::string const &label) -> void { push(label); }},
                arg);
            mstore().push0().mload();
            return *this;
        }

        KernelBuilder &store_address(std::string const &target)
        {
            size_t const offset = address_store.size() * 32;
            auto const [_, inserted] = address_store.insert({target, offset});
            if (!inserted) {
                std::cerr << std::format(
                                 "[store_address] failed to store address of "
                                 "'{}'. Duplicated target?",
                                 target)
                          << std::endl;
                abort();
            }
            push(target).push(static_cast<uint64_t>(offset)).mstore();
            return *this;
        }

        KernelBuilder &load_address(std::string const &target)
        {
            auto const it = address_store.find(target);
            if (it == address_store.end()) {
                std::cerr << std::format(
                                 "[load_address] failed to load address of "
                                 "'{}'. Undefined target?",
                                 target)
                          << std::endl;
                abort();
            }
            push(it->second).mload();
            return *this;
        }

        KernelBuilder &throughput(::EvmBuilder const &sequence)
        {
            comment("Opacify jumpdest addresses")
                .store_address("inner-loop")
                .store_address("inner-cond")
                .comment("Initialize: i = 0, s = 0")
                .push0()
                .push0();

            // Outer loop
            comment("Type: [s, i]")
                .jumpdest("outer-loop")
                .dup2()
                .calldatasize()
                .eq()
                .jumpi("return-result");

            // Data loop
            comment("Push 1000 call data values onto the stack")
                .comment("Type: [s, i] -> [s, i, ...]")
                .jumpdest("data-loop")
                .dup2()
                .calldataload()
                .comment("i += 1")
                .swap2()
                .push(1)
                .add()
                .comment("s += 1")
                .swap1()
                .push(1)
                .add()
                .comment("Repeat if s < 1000")
                .push(1000)
                .dup2()
                .lt()
                .jumpi("data-loop");
            comment("... otherwise perform a dynamic jump to inner-loop")
                .load_address("inner-loop")
                .jump();

            // Inner loop
            comment("Type: [s, i, d1, d2, d3, ..., d20]")
                .jumpdest("inner-loop");
            for (size_t n = 3, i = 1; i <= 10; i++, n++) {
                swap(n).swap1().swap(n - 1).append(sequence);
            }
            load_address("inner-cond").jump();

            // Inner condition loop
            comment("Type: [a10, a4, s, a5, a2, a6, i, a7, a3, a8, a1, a9]")
                .jumpdest("inner-cond")
                .pop()
                .pop()
                .swap9();
            for (size_t i = 0; i < 4; i++) {
                pop();
            }
            swap4();
            for (size_t i = 0; i < 4; i++) {
                pop();
            }
            comment("s -= 20")
                .swap1()
                .push(20)
                .swap1()
                .sub()
                .comment("Jump to inner-loop, if s != 0")
                .dup1()
                .jumpi("inner-loop")
                .pop()
                .push0()
                .jump("outer-loop");

            // Result block
            jumpdest("return-result").stop();

            return *this;
        }

        KernelBuilder &latency(::EvmBuilder const &sequence)
        {
            comment("Opacify jumpdest addresses")
                .store_address("inner-loop")
                .store_address("inner-cond")
                .comment("Initialize: i = 0, s = 0, p = 0")
                .push0()
                .push0()
                .push0(); // [p = 0, s = 0, i = 0]

            // Outer loop
            comment("outer-loop, type: [p, s, i]")
                .jumpdest("outer-loop")
                .dup3()
                .calldatasize()
                .eq()
                .jumpi("return-result")
                .comment("p0 := p")
                .dup1();

            // Data loop
            comment("Push 1000 call data values onto the stack")
                .comment("data-loop, type: [p0, p, s, i]")
                .jumpdest("data-loop")
                .comment("x := calldata(i)")
                .dup4() // [i, p0, p, s, i]
                .calldataload() // [x, p0, p, s, i]
                .dup1() // [x, x, p0, p, s, i]
                .dup4() // [p, x, x, p0, p, s, i]
                .comment("p xor x")
                .xor_() // [(p xor x), x, p0, p, s, i]
                .comment("i += 1")
                .swap5() // [i, x, p0, p, s, (p xor x)]
                .push(1) // [1, i, x, p0, p, s, (p xor x)]
                .add() // [ (1 + i), x, p0, p, s, (p xor x)]
                .comment("y := calldata(1 + i)")
                .dup1() // [ (1 + i), (1 + i), x, p0, p, s, (p xor x)]
                .calldataload() // [ y, (1 + i), x, p0, p, s, (p xor x)]
                .dup1() // [ y, y, (1 + y), x, p0, p, s, (p xor x) ]
                .comment("p xor y")
                .swap5() // [ p, y, (1 + i), x, p0, y, s, (p xor x)]
                .xor_() // [ (p xor y), (1 + i), x, p0, y, s, (p xor x)]
                .comment("p := op(x, y)")
                .swap4() // [ y, (1 + i), x, p0, (p xor y), s, (p xor x)]
                .swap1() // [ (1 + i), y, x, ... ]
                .swap2() // [ x, y, (1 + i), ... ]
                .append(sequence) // [ p = op(x, y), (1 + i), ... ]
                .comment(" i += 1")
                .swap1() // [ (1 + i), p = op(x, y), p0, (p xor y), s, (p xor
                         // x)]
                .push(1)
                .add() // [ (2 + i), p = op(x, y), p0, (p xor y), s, (p xor x)]
                .comment("s += 2")
                .swap3() // [ (p xor y), p = op(x, y), p0, (2 + i), s, (p xor x)
                         // ]
                .swap4() // [ s, p = op(x, y), p0, (2 + i), (p xor y), (p xor x)
                         // ]
                .push(2)
                .add() // [ (2 + s), p = op(x, y), p0, (2 + i), (p xor y), (p
                       // xor x)
                       // ]
                .comment("Move p0 to the front of the stack")
                .swap2() // [ p0, op(x, y), (2 + s), (2 + i), (p xor y), (p xor
                         // x) ]
                .comment("Repeat if s < 1000")
                .push(1000) // [ 1000, p0, p = op(x, y), (2 + s), (2 + i), (p
                            // xor y), (p xor x) ]
                .dup4() // [ (2 + s), 1000, p0, p = op(x, y), (2 + s), (2 + i),
                        // (p xor y), (p xor x) ]
                .lt() // [ 1?, p0, p = op(x, y), (2 + s), (2 + i), (p xor y), (p
                      // xor x) ]
                .jumpi("data-loop") // [ data-loop, 1?, p0, p = op(x, y), (2 +
                                    // s), (2 + i), (p xor y), (p xor x) ]
                .comment("p := p0")
                .swap1() // [ p = op(x, y), p0, (2 + s), (2 + i), (p xor y), (p
                         // xor x) ]
                .pop(); // [ p0, (2 + s), (2 + i), (p xor y), (p xor x) ]
            load_address("inner-loop").jump();

            // Inner loop
            comment("inner-loop, type: [p, s, i, d1, d2, d3, ..., d40]")
                .jumpdest("inner-loop");
            for (size_t i = 0; i < 20; i++) {
                comment(std::format("Instruction sequence {}", i + 1))
                    .swap4() // [d2, s, i, d1, p, d3, ..., d40]
                    .dup5() //  [p, d2, s, i, d1, p, d3, ..., d40]
                    .xor_() // [(p xor d2), s, i, d1, p, d3, ..., d40]
                    .swap2() // [i, s, (p xor d2), d1, p, d3, ..., d40]
                    .swap3() // [d1, s, (p xor d2), i, p, d3, ..., d40]
                    .swap1() // [s, d1, (p xor d2), i, p, d3, ..., d40]
                    .swap4() // [p, d1, (p xor d2), i, s, d3, ..., d40]
                    .xor_() // [ (p xor d1), (p xor d2), i, s, d3, ..., d40 ]
                    .append(sequence); // [ op(p xor d1, p xor d2), i, s, d3,
                                       // ..., d40 ]
            }
            comment("Jump to inner-cond").load_address("inner-cond").jump();

            comment("inner-cond, type: [a, s, i]")
                .jumpdest("inner-cond")
                .swap1() // [s, a, i]
                .push(40) // [ 40, s, a, i ]
                .swap1() //  [ s, 40, a, i ]
                .sub() //  [ (s - 40), a, i ]
                .swap1() //  [ a, (s - 40), i ]
                .dup2() //  [ (s - 40), a, (s - 40), i ]
                .jumpi("inner-loop") // [ inner-loop, (s - 40), a, (s - 40), i ]
                // [a, (s - 40), i]
                .swap1() // [ (s - 40), a, i ]
                .pop() // [ a, i ]
                .push0() // [ 0, a, i ]
                .swap1() // [ a, 0, i ]
                .jump("outer-loop");

            comment("return-result, type: [...]")
                .jumpdest("return-result")
                .stop();

            return *this;
        }

        std::unordered_map<std::string, size_t> address_store{};
    };

    using parameterized_binop_kernel_t = std::function<KernelBuilder(
        uint32_t, runtime::uint256_t, runtime::uint256_t)>;

    parameterized_binop_kernel_t binary_op_micro_kernel(
        compiler::EvmOpCode binop, bool opaque_parameters, bool epilogue)
    {
        return [=](uint32_t i,
                   runtime::uint256_t const &arg1,
                   runtime::uint256_t const &arg2) -> KernelBuilder {
            KernelBuilder eb;
            eb.comment("=== Prologue")
                .prepare_binop_arguments(4, arg1, arg2, opaque_parameters)
                .loop(i, 10, 10, [binop]() {
                    KernelBuilder eb;
                    eb.binop_loop_body(binop);
                    return eb;
                }());
            if (epilogue) {
                eb.epilogue();
            }
            else {
                eb.stop();
            }
            return eb;
        };
    }
}

void emit_kernel(
    emitter_config const &config, EvmBuilder const &eb,
    std::string_view parent_dir, std::string_view name)
{
    auto const dirname =
        monad::test_resource::execution_benchmarks_dir / parent_dir / name;

    if (config.validate && !evm_as::validate(eb)) {
        std::cerr << "validation error: " << dirname << std::endl;
        abort();
    }

    if (!fs::exists(dirname) && !fs::create_directories(dirname)) {
        std::cerr << "cannot create directory " << dirname << std::endl;
        abort();
    }

    std::ofstream contract(
        dirname / "contract",
        std::ios::out | std::ios::binary | std::ios::trunc);
    evm_as::compile(eb, contract);

    std::ofstream contract_mnemonic(
        dirname / "contract.mevm", std::ios::out | std::ios::trunc);
    evm_as::mcompile(eb, contract_mnemonic, config.mconfig);

    std::ofstream const calldata(
        dirname / "calldata",
        std::ios::out | std::ios::binary | std::ios::trunc);
}

void emit_kernels(arguments const &config)
{
    using namespace monad::vm::utils::evm_as::kernels;
    using namespace monad::vm::compiler;
    using namespace monad::vm::runtime;

    emitter_config const em_config{true, {true, true, 32}};

    std::vector<EvmOpCode> const binops = {
        EvmOpCode::ADD,
        EvmOpCode::SUB,
        EvmOpCode::MUL,
        EvmOpCode::DIV,
        EvmOpCode::SDIV,
        EvmOpCode::MOD,
        EvmOpCode::SMOD,
        EvmOpCode::EXP};

    auto const u8_max = std::numeric_limits<uint8_t>::max();
    auto const u16_max = std::numeric_limits<uint16_t>::max();
    auto const u32_max = std::numeric_limits<uint32_t>::max();
    auto const u64_max = std::numeric_limits<uint64_t>::max();
    auto const u128_max = monad::vm::runtime::pow2(128) - 1;
    auto const u256_max = std::numeric_limits<uint256_t>::max();
    std::vector<std::pair<uint256_t, uint256_t>> const parameters = {
        {0, 0},
        {1, 1},
        {u8_max, u16_max},
        {u16_max, monad::vm::runtime::pow2(240)},
        {123456789, 987654321},
        {u64_max, 1},
        {u64_max, 2},
        {u64_max, u32_max},
        {u64_max - 1, u32_max - 1},
        {u128_max, u16_max},
        {u128_max, u16_max - 1},
        {monad::vm::runtime::pow2(255) - 1, monad::vm::runtime::pow2(254)},
        {u256_max, 0}};
    uint32_t const iterations = 1'000'000;

    for (auto binop : binops) {
        size_t i = 0;
        auto const &info = opcode_table<EVMC_LATEST_STABLE_REVISION>[binop];
        for (auto const &[a, b] : parameters) {
            emit_kernel(
                em_config,
                binary_op_micro_kernel(
                    binop, config.opaque_parameters, config.epilogue)(
                    iterations, a, b),
                "basic",
                std::format("binop_{}_{}", info.name, i++));
        }
    }
    emit_kernel(
        em_config,
        binary_op_micro_kernel(
            EvmOpCode::POP, config.opaque_parameters, config.epilogue)(
            iterations, 0, 0),
        "basic",
        "binop_baseline");
}

// The instruction sequences containing vector is passed in by
// reference in `atomic_sequences` and `composite_sequences`, because
// returning them by value causes a false-positive
// `free-nonheap-object` in GCC-15 with optimizations and debug
// assertions enabled.
void atomic_sequences(std::vector<std::pair<std::string, EvmBuilder>> &out)
{
    std::array<std::pair<std::string, EvmBuilder>, 8> const instructions = {
        {{"ADD", evm_as::latest().add()},
         {"SUB", evm_as::latest().sub()},
         {"MUL", evm_as::latest().mul()},
         {"DIV", evm_as::latest().div()},
         {"SDIV", evm_as::latest().sdiv()},
         {"MOD", evm_as::latest().mod()},
         {"SMOD", evm_as::latest().smod()},
         {"EXP", evm_as::latest().exp()}}};

    out.append_range(instructions);
}

void composite_sequences(std::vector<std::pair<std::string, EvmBuilder>> &out)
{
    using T = std::pair<std::string, EvmBuilder>;
    std::vector<T> heads{};
    atomic_sequences(heads);
    std::array<T, 2> const tails = {
        {{"ISZERO", evm_as::latest().iszero()},
         {"NOT", evm_as::latest().not_()}}};

    for (auto const &[hd_name, head] : heads) {
        for (auto const &[tl_name, tail] : tails) {
            std::string const composite_name =
                std::format("{}_{}", hd_name, tl_name);
            out.emplace_back<T>({composite_name, EvmBuilder(head, tail)});
        }
    }
}

void emit_throughput_kernels(arguments const &)
{
    using namespace monad::vm::utils::evm_as::kernels;
    using namespace monad::vm::compiler;
    using namespace monad::vm::utils;

    emitter_config const em_config{false, {true, false, 32}};

    std::vector<std::pair<std::string, EvmBuilder>> sequences{};
    atomic_sequences(sequences);
    composite_sequences(sequences);

    for (auto const &[name, seq] : sequences) {
        KernelBuilder eb{};
        emit_kernel(em_config, eb.throughput(seq), "throughput", name);
    }

    emit_kernel(em_config, evm_as::latest().pop(), "throughput", "baseline");
}

void emit_latency_kernels(arguments const &)
{
    using namespace monad::vm::utils::evm_as::kernels;
    using namespace monad::vm::compiler;
    using namespace monad::vm::utils;

    emitter_config const em_config{false, {true, false, 32}};

    std::vector<std::pair<std::string, EvmBuilder>> sequences{};
    atomic_sequences(sequences);
    composite_sequences(sequences);

    for (auto const &[name, seq] : sequences) {
        KernelBuilder eb{};
        emit_kernel(em_config, eb.throughput(seq), "latency", name);
    }

    emit_kernel(em_config, evm_as::latest().xor_(), "latency", "baseline");
}

int main(int const argc, char **const argv)
{
    auto const config = parse_args(argc, argv);
    emit_kernels(config);
    emit_throughput_kernels(config);
    emit_latency_kernels(config);
    return 0;
}
