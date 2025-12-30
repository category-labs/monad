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

#include <category/vm/utils/evm-as/kernel-builder.hpp>

#include <test/vm/utils/evm-as_utils.hpp>
#include <test/vm/vm/test_vm.hpp>

#include <evmone/test/state/host.hpp>

#include <CLI/CLI.hpp>

#include <algorithm>
#include <cctype>
#include <random>
#include <regex>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::utils::evm_as;

using traits = EvmTraits<EVMC_OSAKA>;

struct CommandArguments
{
    std::vector<std::string> title_filters;
    std::vector<std::string> impl_filters;
    std::vector<std::string> seq_filters;
};

static CommandArguments parse_command_arguments(int argc, char **argv)
{
    auto args = CommandArguments{};

    auto app = CLI::App("Micro benchmarks");
    app.add_option(
        "--title-filter", args.title_filters, "Benchmark title regex");
    app.add_option(
        "--impl-filter", args.impl_filters, "VM implementation regex");
    app.add_option(
        "--seq-filter", args.seq_filters, "Instruction sequence regex");

    try {
        app.parse(argc, argv);
    }
    catch (CLI::CallForHelp const &e) {
        std::exit(app.exit(e));
    }
    return args;
}

static bool
filter_search(std::string const &s, std::vector<std::string> const &filters)
{
    bool enable = filters.empty();
    for (auto const &filter : filters) {
        std::regex r(
            filter,
            std::regex_constants::ECMAScript | std::regex_constants::icase);
        enable |= std::regex_search(s, r);
    }
    return enable;
}

using Assembler =
    std::function<KernelBuilder<traits>(EvmBuilder<traits> const &)>;

using CalldataGenerator =
    std::function<test::KernelCalldata(EvmBuilder<traits> const &)>;

struct Benchmark
{
    std::string title;
    size_t num_inputs;
    bool has_output;
    size_t iteration_count;
    EvmBuilder<traits> baseline_seq;
    std::vector<EvmBuilder<traits>> subject_seqs;
    std::optional<std::vector<EvmBuilder<traits>>> effect_free_subject_seqs;
    size_t sequence_count;
    Assembler assemble;
    CalldataGenerator calldata_generate;
};

static double execute_iteration(
    evmc::VM &vm, evmc::address const &code_address,
    std::vector<uint8_t> const &bytecode, test::KernelCalldata const &calldata)
{
    evmc::address sender_address{200};

    evmone::test::TestState test_state{};
    test_state.apply(evmone::state::StateDiff{
        .modified_accounts =
            {evmone::state::StateDiff::Entry{
                 .addr = code_address,
                 .nonce = 1,
                 .balance = 10 * 30,
                 .code = std::optional<evmc::bytes>{evmc::bytes(
                     bytecode.data(), bytecode.size())},
                 .modified_storage = {}},
             evmone::state::StateDiff::Entry{
                 .addr = sender_address,
                 .nonce = 1,
                 .balance = 10 * 30,
                 .code = {},
                 .modified_storage = {}}},
        .deleted_accounts = {}});
    evmone::state::State host_state{test_state};
    evmone::state::BlockInfo block_info{};
    evmone::test::TestBlockHashes block_hashes{};
    evmone::state::Transaction transaction{};
    auto host = evmone::state::Host(
        traits::evm_rev(),
        vm,
        host_state,
        block_info,
        block_hashes,
        transaction);
    auto *bvm = reinterpret_cast<BlockchainTestVM *>(vm.get_raw_pointer());
    auto const *interface = &host.get_interface();
    auto *ctx = host.to_context();

    evmc_message msg{
        .kind = EVMC_CALL,
        .flags = 0,
        .depth = 0,
        .gas = std::numeric_limits<int64_t>::max(),
        .recipient = code_address,
        .sender = sender_address,
        .input_data = calldata.data(),
        .input_size = calldata.size(),
        .value = {},
        .create2_salt = {},
        .code_address = code_address,
        .memory_handle = nullptr,
        .memory = nullptr,
        .memory_capacity = 0,
    };

    auto const start = std::chrono::steady_clock::now();

    auto result = bvm->execute(
        interface,
        ctx,
        traits::evm_rev(),
        &msg,
        bytecode.data(),
        bytecode.size());

    auto const stop = std::chrono::steady_clock::now();

    MONAD_VM_ASSERT(result.status_code == EVMC_SUCCESS);

    return static_cast<double>((stop - start).count());
}

static std::pair<double, double> execute_against_base(
    evmc::VM &vm, evmc::address const &base_code_address,
    std::vector<uint8_t> const &base_bytecode,
    test::KernelCalldata const &base_calldata,
    evmc::address const &code_address, std::vector<uint8_t> const &bytecode,
    test::KernelCalldata const &calldata, size_t iteration_count)
{
    for (uint32_t i = 0; i < (iteration_count >> 4) + 1; ++i) {
        // warmup
        (void)execute_iteration(
            vm, base_code_address, base_bytecode, base_calldata);
        (void)execute_iteration(vm, code_address, bytecode, calldata);
    }

    double base_best = std::numeric_limits<double>::max();
    double best = std::numeric_limits<double>::max();
    for (size_t i = 0; i < iteration_count; ++i) {
        auto const base_t = execute_iteration(
            vm, base_code_address, base_bytecode, base_calldata);
        base_best = std::min(base_t, base_best);
        auto const t = execute_iteration(vm, code_address, bytecode, calldata);
        best = std::min(t, best);
    }
    return {base_best, best};
}

static void run_implementation_benchmark(
    CommandArguments const &args, BlockchainTestVM::Implementation impl,
    Benchmark const &bench)
{
    auto *bvm = new BlockchainTestVM{impl};
    auto vm = evmc::VM(bvm);

    auto const impl_name = BlockchainTestVM::impl_name(bvm->implementation());

    if (!filter_search(std::string{impl_name}, args.impl_filters)) {
        return;
    }

    uint256_t code_address{1000};
    uint256_t const base_code_address{code_address};

    auto const baseline_mcompile_name = mcompile(bench.baseline_seq);
    auto const base_name = std::all_of(
                               baseline_mcompile_name.begin(),
                               baseline_mcompile_name.end(),
                               [](char c) { return std::isspace(c); })
                               ? std::string{"(empty)\n"}
                               : baseline_mcompile_name;
    std::vector<uint8_t> base_bytecode;
    compile(bench.assemble(bench.baseline_seq), base_bytecode);
    auto const base_calldata = bench.calldata_generate(bench.baseline_seq);

    bool is_title_printed = false;
    auto const seq_count = static_cast<double>(bench.sequence_count);

    for (size_t i = 0; i < bench.subject_seqs.size(); ++i) {
        auto const &seq = bench.subject_seqs[i];
        auto const start = std::chrono::steady_clock::now();

        auto const name = mcompile(seq);
        if (!filter_search(name, args.seq_filters)) {
            continue;
        }

        if (!is_title_printed) {
            std::cout << impl_name << "\n\t" << bench.title
                      << "\n\nBaseline sequence\n"
                      << base_name << "\nResults\n";
            is_title_printed = true;
        }

        code_address = code_address + 1;
        std::vector<uint8_t> bytecode;
        compile(bench.assemble(seq), bytecode);
        auto const calldata = [&] {
            if (auto const &ss = bench.effect_free_subject_seqs) {
                MONAD_VM_ASSERT(ss->size() == bench.subject_seqs.size());
                return bench.calldata_generate((*ss)[i]);
            }
            else {
                return bench.calldata_generate(seq);
            }
        }();

        auto const [base_time, time] = execute_against_base(
            vm,
            address_from_uint256(base_code_address),
            base_bytecode,
            base_calldata,
            address_from_uint256(code_address),
            bytecode,
            calldata,
            bench.iteration_count);

        auto const stop = std::chrono::steady_clock::now();

        std::cout << name << "\tbaseline:  " << (base_time / 1'000'000)
                  << " ms\n"
                  << "\tbest:      " << (time / 1'000'000) << " ms\n"
                  << "\tseq delta: " << ((time - base_time) / seq_count)
                  << " ns\n"
                  << "\ttotal:     " << ((stop - start).count() / 1'000'000)
                  << " ms\n";
    }

    if (is_title_printed) {
        std::cout << '\n';
    }
}

using enum BlockchainTestVM::Implementation;

static BlockchainTestVM::Implementation const all_impls[] = {
    Interpreter,
    BlockchainTestVM::Implementation::Compiler,
    Evmone,
#ifdef MONAD_COMPILER_LLVM
    LLVM,
#endif
};

static void run_benchmark(CommandArguments const &args, Benchmark const &bench)
{
    if (!filter_search(bench.title, args.title_filters)) {
        return;
    }
    for (auto const impl : all_impls) {
        run_implementation_benchmark(args, impl, bench);
    }
}

static std::vector<EvmBuilder<traits>> const basic_una_math_builders = {
    EvmBuilder<traits>{}.iszero(),
    EvmBuilder<traits>{}.not_(),
    EvmBuilder<traits>{}.clz()};

static std::vector<EvmBuilder<traits>> const basic_bin_math_builders = {
    EvmBuilder<traits>{}.add(),
    EvmBuilder<traits>{}.mul(),
    EvmBuilder<traits>{}.sub(),
    EvmBuilder<traits>{}.div(),
    EvmBuilder<traits>{}.sdiv(),
    EvmBuilder<traits>{}.mod(),
    EvmBuilder<traits>{}.smod(),
    EvmBuilder<traits>{}.lt(),
    EvmBuilder<traits>{}.gt(),
    EvmBuilder<traits>{}.slt(),
    EvmBuilder<traits>{}.sgt(),
    EvmBuilder<traits>{}.eq(),
    EvmBuilder<traits>{}.and_(),
    EvmBuilder<traits>{}.or_(),
    EvmBuilder<traits>{}.xor_(),
};

static std::vector<EvmBuilder<traits>> const basic_tern_math_builders = {
    EvmBuilder<traits>{}.addmod(), EvmBuilder<traits>{}.mulmod()};

static std::vector<EvmBuilder<traits>> const exp_bin_math_builder = {
    EvmBuilder<traits>{}.exp()};

static std::vector<EvmBuilder<traits>> const byte_bin_math_builders = {
    EvmBuilder<traits>{}.signextend(), EvmBuilder<traits>{}.byte()};

static std::vector<EvmBuilder<traits>> const any_shift_math_builders = {
    EvmBuilder<traits>{}.shl(),
    EvmBuilder<traits>{}.shr(),
    EvmBuilder<traits>{}.sar()};

static std::vector<EvmBuilder<traits>> operator*(
    std::vector<EvmBuilder<traits>> const &post, EvmBuilder<traits> const &pre)
{
    std::vector<EvmBuilder<traits>> ret;
    for (auto const &q : post) {
        EvmBuilder<traits> b;
        b.append(pre).append(q);
        ret.push_back(std::move(b));
    }
    return ret;
}

static std::vector<EvmBuilder<traits>> operator*(
    std::vector<EvmBuilder<traits>> const &post,
    std::vector<EvmBuilder<traits>> const &pre)
{
    std::vector<EvmBuilder<traits>> ret;
    for (auto const &p : pre) {
        for (auto const &q : post) {
            EvmBuilder<traits> b;
            b.append(p).append(q);
            ret.push_back(std::move(b));
        }
    }
    return ret;
}

static uint256_t rand_uint256()
{
    static std::random_device rd;
    static std::mt19937 gen(rd());
    static std::uniform_int_distribution<uint64_t> d(
        0, std::numeric_limits<uint64_t>::max());
    return {d(gen), d(gen), d(gen), d(gen)};
}

struct BenchmarkBuilderData
{
    std::string title;
    size_t num_inputs;
    bool has_output;
    size_t iteration_count;
    std::optional<EvmBuilder<traits>> baseline_seq = std::nullopt;
    std::vector<EvmBuilder<traits>> subject_seqs;
    std::optional<std::vector<EvmBuilder<traits>>> effect_free_subject_seqs =
        std::nullopt;
};

struct BenchmarkBuilder
{
    BenchmarkBuilder(CommandArguments const &args, BenchmarkBuilderData data)
        : command_arguments_{args}
        , title_{std::move(data.title)}
        , num_inputs_{data.num_inputs}
        , has_output_{data.has_output}
        , iteration_count_{data.iteration_count}
        , baseline_seq_{std::move(data.baseline_seq)}
        , subject_seqs_{std::move(data.subject_seqs)}
        , effect_free_subject_seqs_{std::move(data.effect_free_subject_seqs)}
    {
    }

    BenchmarkBuilder &
    make_calldata(std::function<std::vector<uint8_t>(size_t)> f)
    {
        calldata_ = f(num_inputs_);
        return *this;
    }

    BenchmarkBuilder &run_throughput_benchmark();
    BenchmarkBuilder &run_latency_benchmark();

private:
    CommandArguments command_arguments_;
    std::string title_;
    size_t num_inputs_;
    bool has_output_;
    size_t iteration_count_;
    std::optional<EvmBuilder<traits>> baseline_seq_;
    std::vector<EvmBuilder<traits>> subject_seqs_;
    std::optional<std::vector<EvmBuilder<traits>>> effect_free_subject_seqs_;
    std::vector<uint8_t> calldata_;
};

BenchmarkBuilder &BenchmarkBuilder::run_throughput_benchmark()
{
    using KB = KernelBuilder<traits>;

    MONAD_VM_ASSERT(calldata_.size());

    KB base_builder;
    for (size_t i = 1; i < num_inputs_; ++i) {
        base_builder.pop();
    }
    if (!num_inputs_ && has_output_) {
        base_builder.push0();
    }

    run_benchmark(
        command_arguments_,
        Benchmark{
            .title = title_ + ", throughput",
            .num_inputs = num_inputs_,
            .has_output = has_output_,
            .iteration_count = iteration_count_,
            .baseline_seq = baseline_seq_.has_value() ? *baseline_seq_
                                                      : std::move(base_builder),
            .subject_seqs = subject_seqs_,
            .effect_free_subject_seqs = effect_free_subject_seqs_,
            .sequence_count = KB::get_sequence_repetition_count(
                num_inputs_, calldata_.size()),
            .assemble =
                [this](auto const &seq) {
                    return KB{}.throughput(seq, num_inputs_, has_output_);
                },
            .calldata_generate =
                [this](auto const &) {
                    return test::to_throughput_calldata<traits>(
                        num_inputs_, calldata_);
                }});

    return *this;
}

BenchmarkBuilder &BenchmarkBuilder::run_latency_benchmark()
{
    using KB = KernelBuilder<traits>;

    MONAD_VM_ASSERT(calldata_.size());
    MONAD_VM_ASSERT(has_output_);
    MONAD_VM_ASSERT(num_inputs_ >= 1);

    KB base_builder;
    if (num_inputs_ == 1) {
        base_builder.not_();
    }
    else {
        for (size_t i = 1; i < num_inputs_; ++i) {
            base_builder.xor_();
        }
    }

    run_benchmark(
        command_arguments_,
        Benchmark{
            .title = title_ + ", latency",
            .num_inputs = num_inputs_,
            .has_output = has_output_,
            .iteration_count = iteration_count_,
            .baseline_seq = baseline_seq_.has_value() ? *baseline_seq_
                                                      : std::move(base_builder),
            .subject_seqs = subject_seqs_,
            .effect_free_subject_seqs = effect_free_subject_seqs_,
            .sequence_count = KB::get_sequence_repetition_count(
                num_inputs_, calldata_.size()),
            .assemble =
                [this](auto const &seq) {
                    return KB{}.latency(seq, num_inputs_);
                },
            .calldata_generate =
                [this](auto const &seq) {
                    return test::to_latency_calldata(
                        seq,
                        num_inputs_,
                        test::to_throughput_calldata<traits>(
                            num_inputs_, calldata_));
                }});

    return *this;
}

int main(int argc, char **argv)
{
    auto const args = parse_command_arguments(argc, argv);

    BenchmarkBuilder(
        args,
        {.title = "BASIC_UNA_MATH, constant input",
         .num_inputs = 1,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_una_math_builders})
        .make_calldata([](size_t num_inputs) {
            return std::vector<uint8_t>(10'000 * num_inputs * 32, 1);
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "DUP2; MSTORE; MLOAD, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = {KernelBuilder<traits>{}.dup2().mstore().mload()},
         .effect_free_subject_seqs = {{KernelBuilder<traits>{}.pop()}}})
        .make_calldata([](size_t num_inputs) {
            auto const off = KernelBuilder<traits>::free_memory_start;
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                uint256_t{off}.store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "DUP2; MSTORE; MLOAD, increasing input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = {KernelBuilder<traits>{}.dup2().mstore().mload()},
         .effect_free_subject_seqs = {{KernelBuilder<traits>{}.pop()}}})
        .make_calldata([](size_t num_inputs) {
            auto const off = KernelBuilder<traits>::free_memory_start;
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                uint256_t{off + i * 2}.store_be(&cd[i]);
                uint256_t{off + i * 2}.store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            return std::vector<uint8_t>(10'000 * num_inputs * 32, 1);
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "EXP, random input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 30,
         .subject_seqs = exp_bin_math_builder})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(4'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                rand_uint256().store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BYTE/SIGNEXTEND, random input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = byte_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(100'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                (rand_uint256() & 31).store_be(&cd[i]);
                rand_uint256().store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BYTE/SIGNEXTEND, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = byte_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                uint256_t{3}.store_be(&cd[i]);
                uint256_t{-1, -1, -1, -1}.store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "PUSH 23; SIGNEXTEND, constant input",
         .num_inputs = 1,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = {EvmBuilder<traits>{}.push(23).signextend()}})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                uint256_t{3}.store_be(&cd[i]);
                uint256_t{-1, -1, -1, -1}.store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "PUSH 1; XOR; PUSH 23; SIGNEXTEND, constant input",
         .num_inputs = 1,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs =
             {EvmBuilder<traits>{}.push(1).xor_().push(23).signextend()}})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                uint256_t{3}.store_be(&cd[i]);
                uint256_t{-1, -1, -1, -1}.store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "SHIFT, random input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 10,
         .subject_seqs = any_shift_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(100'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                (rand_uint256() & 255).store_be(&cd[i]);
                rand_uint256().store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "SHIFT, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = any_shift_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 64) {
                uint256_t{129}.store_be(&cd[i]);
                uint256_t{-1, -1, -1, -1}.store_be(&cd[i + 32]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_TERN_MATH, random input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_tern_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                rand_uint256().store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH; BASIC_BIN_MATH, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders * basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            return std::vector<uint8_t>(10'000 * num_inputs * 32, 1);
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_UNA_MATH; BASIC_BIN_MATH, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders * basic_una_math_builders})
        .make_calldata([](size_t num_inputs) {
            return std::vector<uint8_t>(10'000 * num_inputs * 32, 1);
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH; BASIC_UNA_MATH, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_una_math_builders * basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            return std::vector<uint8_t>(10'000 * num_inputs * 32, 1);
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "SHIFT; BASIC_BIN_MATH, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders * any_shift_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                uint256_t{77}.store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "SHIFT; SWAP1; BASIC_BIN_MATH, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders *
                         KernelBuilder<traits>{}.swap1() *
                         any_shift_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                uint256_t{77}.store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH; SHIFT, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = any_shift_math_builders * basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 100 * 32) {
                for (size_t j = 0; j < 100; ++j) {
                    uint256_t{j}.store_be(&cd[i + 32 * j]);
                }
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH; SWAP1; SHIFT, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = any_shift_math_builders *
                         KernelBuilder<traits>{}.swap1() *
                         basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 100 * 32) {
                for (size_t j = 0; j < 100; ++j) {
                    uint256_t{j}.store_be(&cd[i + 32 * j]);
                }
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BYTE/SIGNEXTEND; BASIC_BIN_MATH, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders * byte_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                uint256_t{22}.store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BYTE/SIGNEXTEND; SWAP1; BASIC_BIN_MATH, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = basic_bin_math_builders *
                         KernelBuilder<traits>{}.swap1() *
                         byte_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 32) {
                uint256_t{22}.store_be(&cd[i]);
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH; BYTE/SIGNEXTEND, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = byte_bin_math_builders * basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 30 * 32) {
                for (size_t j = 0; j < 30; ++j) {
                    uint256_t{j}.store_be(&cd[i + 32 * j]);
                }
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "BASIC_BIN_MATH; SWAP1; BYTE/SIGNEXTEND, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = byte_bin_math_builders *
                         KernelBuilder<traits>{}.swap1() *
                         basic_bin_math_builders})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 30 * 32) {
                for (size_t j = 0; j < 30; ++j) {
                    uint256_t{j}.store_be(&cd[i + 32 * j]);
                }
            }
            return cd;
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "CREATE, constant input",
         .num_inputs = 3,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = {KernelBuilder<traits>{}.create()}})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += 96) {
                uint256_t{0}.store_be(&cd[i]); // value
                uint256_t{32}.store_be(&cd[i + 32]); // offset
                uint256_t{32}.store_be(&cd[i + 64]); // size
            }
            return cd;
        })
        .run_throughput_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "CALL, constant input",
         .num_inputs = 7,
         .has_output = true,
         .iteration_count = 100,
         .subject_seqs = {KernelBuilder<traits>{}.call()}})
        .make_calldata([](size_t num_inputs) {
            std::vector<uint8_t> cd(10'000 * num_inputs * 32, 0);
            for (size_t i = 0; i < cd.size(); i += num_inputs * 32) {
                uint256_t{100'000}.store_be(&cd[i]); // gas
                uint256_t{0}.store_be(&cd[i + 32]); // address
                uint256_t{0}.store_be(&cd[i + 64]); // value
                uint256_t{0}.store_be(&cd[i + 96]); // argsOffset
                uint256_t{64}.store_be(&cd[i + 128]); // argsSize
                uint256_t{64}.store_be(&cd[i + 160]); // retOffset
                uint256_t{32}.store_be(&cd[i + 192]); // retSize
            }
            return cd;
        })
        .run_throughput_benchmark();

    BenchmarkBuilder(
        args,
        {.title = "store forwarding stall, constant input",
         .num_inputs = 2,
         .has_output = true,
         .iteration_count = 100,
         .baseline_seq = KernelBuilder<traits>{}
                             .dup2()
                             .dup2()
                             .add()
                             .dup3()
                             .dup3()
                             .add()
                             .dup4()
                             .dup4()
                             .add()
                             .dup5()
                             .dup5()
                             .add()
                             .dup6()
                             .dup6()
                             .add()
                             .dup7()
                             .dup7()
                             .add()
                             .dup8()
                             .dup8()
                             .add()
                             .dup7()
                             .dup5()
                             .add()
                             .add()
                             .add()
                             .add()
                             .add()
                             .add()
                             .add()
                             .add()
                             .add()
                             .add(),
         .subject_seqs = {KernelBuilder<traits>{}
                              .dup2()
                              .dup2()
                              .add()
                              .dup3()
                              .dup3()
                              .add()
                              .dup4()
                              .dup4()
                              .add()
                              .dup5()
                              .dup5()
                              .add()
                              .dup6()
                              .dup6()
                              .add()
                              .dup7()
                              .dup7()
                              .add()
                              .dup8()
                              .dup8()
                              .add()
                              .dup7()
                              .dup5()
                              .xor_() // add() in the baseline
                              .add()
                              .add()
                              .add()
                              .add()
                              .add()
                              .add()
                              .add()
                              .add()
                              .add()},
         .effect_free_subject_seqs = {{KernelBuilder<traits>{}.pop()}}})
        .make_calldata([](size_t num_inputs) {
            return std::vector<uint8_t>(10'000 * num_inputs * 32, 1);
        })
        .run_throughput_benchmark()
        .run_latency_benchmark();
}
