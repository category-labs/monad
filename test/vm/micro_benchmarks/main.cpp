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
#include <iomanip>
#include <random>
#include <regex>

using namespace monad;
using namespace monad::vm;
using namespace monad::vm::runtime;
using namespace monad::vm::utils::evm_as;

using traits = EvmTraits<EVMC_OSAKA>;

enum class OutputFormat
{
    List,
    Org,
    Markdown
};

std::map<std::string, OutputFormat> const format_map = {
    {"list", OutputFormat::List},
    {"org", OutputFormat::Org},
    {"md", OutputFormat::Markdown}};

struct CommandArguments
{
    std::vector<std::string> title_filters;
    std::vector<std::string> impl_filters;
    std::vector<std::string> seq_filters;
    OutputFormat format = OutputFormat::List;
    bool verbose = false;
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
    app.add_option("--format", args.format, "Output format: list, org, md")
        ->transform(CLI::CheckedTransformer(format_map, CLI::ignore_case));
    app.add_flag(
        "--verbose", args.verbose, "Print benchmark progress information");

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

struct SeqResult
{
    std::string subj_seq;
    double baseline;
    double best;
    double delta;
    std::chrono::steady_clock::rep total;
};

struct BenchmarkResult
{
    std::string impl;
    std::string title;
    std::string base_seq;
    std::vector<SeqResult> results{};

    void add(SeqResult res)
    {
        std::replace(res.subj_seq.begin(), res.subj_seq.end(), '\n', ';');
        results.push_back(res);
    }

    bool empty() const
    {
        return results.empty();
    }
};

// Table formatting for Org-mode and Markdown output
class TableFormatter
{
    struct ColumnSpec
    {
        std::string name;
        size_t width;
        bool left_align;
    };

    static inline size_t const default_seq_width = 10;

    std::vector<ColumnSpec> columns_{
        {.name = "Subj Seq", .width = default_seq_width, .left_align = true},
        {.name = "Baseline (ms)", .width = 13, .left_align = false},
        {.name = "Best (ms)", .width = 10, .left_align = false},
        {.name = "Seq Delta (ns)", .width = 14, .left_align = false},
        {.name = "Total (ms)", .width = 10, .left_align = false},
    };

    OutputFormat format_;

public:
    explicit TableFormatter(OutputFormat format)
        : format_{format}
    {
    }

    void compute_column_widths(BenchmarkResult const &r)
    {
        columns_[0].width = default_seq_width;

        for (auto const &seq : r.results) {
            columns_[0].width =
                std::max(columns_[0].width, seq.subj_seq.length());
        }

        // Ensure column is at least as wide as the header
        columns_[0].width =
            std::max(columns_[0].width, columns_[0].name.length());
    }

    void print_header(BenchmarkResult const &r)
    {
        std::cout << r.impl << "\n\t" << r.title << "\n\nBaseline sequence\n"
                  << r.base_seq << "\nResults\n";

        print_table_header();
    }

    void print_table_header()
    {
        for (auto const &col : columns_) {
            std::cout << "| " << std::setw(static_cast<int>(col.width))
                      << (col.left_align ? std::left : std::right) << col.name
                      << " ";
        }
        std::cout << "|" << std::endl;

        print_separator_line();
    }

    void print_separator_line()
    {
        if (format_ == OutputFormat::Org) {
            // Org-mode: |---+---+---|
            std::cout << "|";
            for (size_t i = 0; i < columns_.size(); ++i) {
                std::cout << std::string(columns_[i].width + 2, '-');
                std::cout << (i < columns_.size() - 1 ? "+" : "|");
            }
            std::cout << std::endl;
        }
        else {
            // Markdown: | :--- | ---: |
            for (auto const &col : columns_) {
                std::cout << "| ";
                if (col.left_align) {
                    std::cout << ":";
                    std::cout << std::string(col.width - 1, '-');
                    std::cout << " ";
                }
                else {
                    std::cout << std::string(col.width - 1, '-');
                    std::cout << ": ";
                }
            }
            std::cout << "|" << std::endl;
        }
    }

    void print_row(SeqResult const &s)
    {
        std::cout << "| " << std::left
                  << std::setw(static_cast<int>(columns_[0].width))
                  << s.subj_seq << " ";

        std::cout << std::right << std::fixed << std::setprecision(6);

        std::cout << "| " << std::setw(static_cast<int>(columns_[1].width))
                  << s.baseline << " ";

        std::cout << "| " << std::setw(static_cast<int>(columns_[2].width))
                  << s.best << " ";

        std::cout << std::setprecision(5);
        std::cout << "| " << std::setw(static_cast<int>(columns_[3].width))
                  << s.delta << " ";

        std::cout << "| " << std::setw(static_cast<int>(columns_[4].width))
                  << s.total << " ";

        std::cout << "|" << std::endl;
    }

    void print_benchmark(BenchmarkResult const &r)
    {
        if (r.empty()) {
            return;
        }

        compute_column_widths(r);
        print_header(r);

        for (auto const &seq : r.results) {
            print_row(seq);
        }
        std::cout << std::endl;
    }
};

class ListFormatter
{
public:
    void print_benchmark(BenchmarkResult const &r)
    {
        if (r.empty()) {
            return;
        }

        std::cout << r.impl << "\n\t" << r.title << "\n\nBaseline sequence\n"
                  << r.base_seq << "\nResults\n";

        for (auto const &s : r.results) {
            std::cout << s.subj_seq << "\n"
                      << std::fixed << std::setprecision(6)
                      << "\tbaseline:  " << s.baseline << " ms\n"
                      << "\tbest:      " << s.best << " ms\n"
                      << std::setprecision(5) << "\tseq delta: " << s.delta
                      << " ns\n"
                      << "\ttotal:     " << s.total << " ms\n";
        }
        std::cout << std::endl;
    }
};

static void
print_results(std::vector<BenchmarkResult> const &results, OutputFormat format)
{
    if (format == OutputFormat::List) {
        ListFormatter formatter;
        for (auto const &r : results) {
            formatter.print_benchmark(r);
        }
    }
    else {
        TableFormatter formatter(format);
        for (auto const &r : results) {
            formatter.print_benchmark(r);
        }
    }
}

static double execute_iteration(
    evmc::VM &vm, MemoryPool &memory_pool, evmc::address const &code_address,
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

    auto msg_memory = memory_pool.alloc_ref();
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
        .memory_handle = msg_memory.get(),
        .memory = msg_memory.get(),
        .memory_capacity = memory_pool.alloc_capacity(),
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
    evmc::VM &vm, MemoryPool &memory_pool,
    evmc::address const &base_code_address,
    std::vector<uint8_t> const &base_bytecode,
    test::KernelCalldata const &base_calldata,
    evmc::address const &code_address, std::vector<uint8_t> const &bytecode,
    test::KernelCalldata const &calldata, size_t iteration_count)
{
    for (uint32_t i = 0; i < (iteration_count >> 4) + 1; ++i) {
        // warmup
        (void)execute_iteration(
            vm, memory_pool, base_code_address, base_bytecode, base_calldata);
        (void)execute_iteration(
            vm, memory_pool, code_address, bytecode, calldata);
    }

    double base_best = std::numeric_limits<double>::max();
    double best = std::numeric_limits<double>::max();
    for (size_t i = 0; i < iteration_count; ++i) {
        auto const base_t = execute_iteration(
            vm, memory_pool, base_code_address, base_bytecode, base_calldata);
        base_best = std::min(base_t, base_best);
        auto const t = execute_iteration(
            vm, memory_pool, code_address, bytecode, calldata);
        best = std::min(t, best);
    }
    return {base_best, best};
}

static std::optional<BenchmarkResult> run_implementation_benchmark(
    CommandArguments const &args, BlockchainTestVM::Implementation impl,
    MemoryPool &memory_pool, Benchmark const &bench)
{
    auto *bvm = new BlockchainTestVM{impl};
    auto vm = evmc::VM(bvm);

    auto const impl_name =
        std::string{BlockchainTestVM::impl_name(bvm->implementation())};

    if (!filter_search(impl_name, args.impl_filters)) {
        return {};
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

    BenchmarkResult res{
        .impl = impl_name, .title = bench.title, .base_seq = base_name};
    auto const seq_count = static_cast<double>(bench.sequence_count);

    for (size_t i = 0; i < bench.subject_seqs.size(); ++i) {
        auto const &seq = bench.subject_seqs[i];
        auto const start = std::chrono::steady_clock::now();

        auto const name = mcompile(seq);
        if (!filter_search(name, args.seq_filters)) {
            continue;
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
            memory_pool,
            address_from_uint256(base_code_address),
            base_bytecode,
            base_calldata,
            address_from_uint256(code_address),
            bytecode,
            calldata,
            bench.iteration_count);

        auto const stop = std::chrono::steady_clock::now();

        res.add(
            {.subj_seq = name,
             .baseline = base_time / 1'000'000,
             .best = time / 1'000'000,
             .delta = ((time - base_time) / seq_count),
             .total = ((stop - start).count() / 1'000'000)});
    }

    return res;
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

static void run_benchmark(
    CommandArguments const &args, std::vector<BenchmarkResult> &results,
    MemoryPool &memory_pool, Benchmark const &bench)
{
    if (!filter_search(bench.title, args.title_filters)) {
        return;
    }
    if (args.verbose) {
        std::cout << bench.title << "...";
    }
    for (auto const impl : all_impls) {
        if (auto res =
                run_implementation_benchmark(args, impl, memory_pool, bench)) {
            if (args.verbose) {
                std::cout << res.value().impl << "...";
            }
            results.push_back(res.value());
        }
    }
    if (args.verbose) {
        std::cout << std::endl;
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
    BenchmarkBuilder(
        CommandArguments const &args, std::vector<BenchmarkResult> &results,
        BenchmarkBuilderData data)
        : command_arguments_{args}
        , results_{results}
        , title_{std::move(data.title)}
        , num_inputs_{data.num_inputs}
        , has_output_{data.has_output}
        , iteration_count_{data.iteration_count}
        , baseline_seq_{std::move(data.baseline_seq)}
        , subject_seqs_{std::move(data.subject_seqs)}
        , effect_free_subject_seqs_{std::move(data.effect_free_subject_seqs)}
        , memory_pool_{100 * 1024} // arbitrary 100 kB alloc capacity
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
    std::vector<BenchmarkResult> &results_;
    std::string title_;
    size_t num_inputs_;
    bool has_output_;
    size_t iteration_count_;
    std::optional<EvmBuilder<traits>> baseline_seq_;
    std::vector<EvmBuilder<traits>> subject_seqs_;
    std::optional<std::vector<EvmBuilder<traits>>> effect_free_subject_seqs_;
    std::vector<uint8_t> calldata_;
    MemoryPool memory_pool_;
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
        results_,
        memory_pool_,
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
        results_,
        memory_pool_,
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
    std::vector<BenchmarkResult> results;

    BenchmarkBuilder(
        args,
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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
        results,
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

    print_results(results, args.format);

    return 0;
}
