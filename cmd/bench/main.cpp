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

// monad-bench: benchmarks a graph for the graph-eval precompile, or EVM
// bytecode, in each engine that can run it, on one thread.
//
//     monad-bench <file.graph | file.bc> [file.dat] <modes...> [options]
//
// A .bc file is EVM runtime bytecode, and a .dat file calldata, both in hex,
// where whitespace and a leading 0x are ignored. Bytecode runs in the monad
// VM's interpreter (--interpreted) or its native compiler (--compiled), as the
// code of an account, with the storage in --storage's file, that a sender
// calls with the calldata, under a Monad revision (--revision). Each call
// starts from the same state, in a State of its own. Calls the code makes to
// other accounts are interpreted in both modes.
//
// A .graph file is the graph language graph_fixture.py parses, which
// graph_inputs.py runs it through. Its inputs are those of one of its calls
// (--call), or those in the evalGraph or evalGraphInto calldata in a .dat
// file. The graph runs in the interpreter (--interpreted), compiled with IREE
// (--iree), or compiled with Halide, with the hand-written schedule
// (--halide) or an autoscheduler (--halide-mullapudi2016, --halide-adams2019,
// --halide-li2018). Each call is timed from the inputs, decoded, in memory, to
// the outputs written, in the same way for each engine: the interpreter copies
// the inputs into its arena, as the precompile does, and a compiled graph is
// given copies of them made in the call, aligned.
//
// Each mode's results are checked before and after it's timed: a graph's
// outputs against the reference evaluator's, or the interpreter's without it
// (--no-reference, or a .dat file), and bytecode's status, gas and output
// against the first call's, and its output against the one in --expect's
// file, if given. Each mode is timed in batches of calls of about a
// millisecond, after a warm-up, for a set time, and the time per call is
// reported as the minimum, median, 90th percentile and maximum over the
// batches. Compiling is timed apart, once; Halide's first compile in a
// process includes its JIT's one-time setup, of about 0.4 s.

#include <category/core/address.hpp>
#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/contract/abi_decode.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/contract/big_endian.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/monad/chain/monad_devnet.hpp>
#include <category/execution/monad/graph_eval/constants.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>
#include <category/execution/monad/graph_eval/references.hpp>
#include <category/execution/monad/graph_eval/tensor.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/monad/revision.h>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/vm.hpp>
#include <test/utils/json_state.hpp>
#include <test/utils/test_state.hpp>
#include <test/vm/utils/test_block_hash_buffer.hpp>
#include <test/vm/utils/test_host.hpp>

#ifdef MONAD_BENCH_IREE
    #include <category/execution/monad/graph_eval/compiler.hpp>
#endif
#ifdef MONAD_BENCH_HALIDE
    #include <category/execution/monad/graph_eval/halide_compiler.hpp>
#endif

#include <CLI/CLI.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <sched.h>

#include <algorithm>
#include <array>
#include <bit>
#include <cctype>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iterator>
#include <memory>
#include <optional>
#include <span>
#include <sstream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::graph_eval;

// The interpreter reads little-endian inputs, and the compiled graphs host
// order ones, and the same bytes are given to both
static_assert(std::endian::native == std::endian::little);

namespace
{
    [[noreturn]] void die(std::string const &message)
    {
        std::fprintf(stderr, "monad-bench: %s\n", message.c_str());
        std::exit(1);
    }

    std::string read_text(std::filesystem::path const &path)
    {
        std::ifstream in(path, std::ios::binary);
        if (!in) {
            die("can't read " + path.string());
        }
        return {std::istreambuf_iterator<char>(in), {}};
    }

    // A file of hex, ignoring whitespace and a leading 0x
    byte_string read_hex(std::filesystem::path const &path)
    {
        std::string hex;
        for (char const c : read_text(path)) {
            if (!std::isspace(static_cast<unsigned char>(c))) {
                hex.push_back(c);
            }
        }
        std::string_view digits{hex};
        if (digits.starts_with("0x") || digits.starts_with("0X")) {
            digits.remove_prefix(2);
        }
        auto bytes = from_hex(digits);
        if (!bytes) {
            die(path.string() + " isn't hex");
        }
        return std::move(*bytes);
    }

    std::string format_time(double const ns)
    {
        char s[32];
        if (ns < 1e3) {
            std::snprintf(s, sizeof s, "%.1f ns", ns);
        }
        else if (ns < 1e6) {
            std::snprintf(s, sizeof s, "%.2f us", ns / 1e3);
        }
        else if (ns < 1e9) {
            std::snprintf(s, sizeof s, "%.3f ms", ns / 1e6);
        }
        else {
            std::snprintf(s, sizeof s, "%.3f s", ns / 1e9);
        }
        return s;
    }

    //
    // Timing
    //

    struct Timing
    {
        double seconds = 2.0;
        double warmup = 0.2;
        size_t min_batches = 10;
    };

    using Clock = std::chrono::steady_clock;

    double elapsed_ns(Clock::time_point const since)
    {
        return std::chrono::duration<double, std::nano>(Clock::now() - since)
            .count();
    }

    // Times `call`, after a warm-up, in batches of about a millisecond, of at
    // most `max_batch` calls, and reports the time per call. `prepare(n)` sets
    // up the next n calls, untimed, and `call(i)` makes the i-th
    void measure(
        std::string const &name, Timing const &timing, size_t const max_batch,
        std::function<void(size_t)> const &prepare,
        std::function<void(size_t)> const &call)
    {
        prepare(1);
        auto const first = Clock::now();
        call(0);
        double const one = std::max(elapsed_ns(first), 1.0);
        size_t const batch = std::clamp<size_t>(
            static_cast<size_t>(1e6 / one), size_t{1}, max_batch);

        auto const warmup = Clock::now();
        while (elapsed_ns(warmup) < timing.warmup * 1e9) {
            prepare(batch);
            for (size_t i = 0; i < batch; i++) {
                call(i);
            }
        }

        std::vector<double> per_call;
        auto const start = Clock::now();
        while (per_call.size() < timing.min_batches ||
               elapsed_ns(start) < timing.seconds * 1e9) {
            prepare(batch);
            auto const batch_start = Clock::now();
            for (size_t i = 0; i < batch; i++) {
                call(i);
            }
            per_call.push_back(
                elapsed_ns(batch_start) / static_cast<double>(batch));
        }
        std::sort(per_call.begin(), per_call.end());
        auto const at = [&](double const q) {
            return per_call[std::min(
                per_call.size() - 1,
                static_cast<size_t>(q * static_cast<double>(per_call.size())))];
        };
        std::printf(
            "%-22s %11s %11s %11s %11s   %zu batches of %zu\n",
            name.c_str(),
            format_time(per_call.front()).c_str(),
            format_time(at(0.5)).c_str(),
            format_time(at(0.9)).c_str(),
            format_time(per_call.back()).c_str(),
            per_call.size(),
            batch);
        std::fflush(stdout);
    }

    void print_header()
    {
        std::printf(
            "%-22s %11s %11s %11s %11s\n",
            "per call",
            "min",
            "median",
            "p90",
            "max");
    }

    void print_compile(std::string const &name, double const ns)
    {
        std::printf(
            "%-22s compiled in %s\n", name.c_str(), format_time(ns).c_str());
        std::fflush(stdout);
    }

    //
    // The machine
    //

    std::string first_line(std::filesystem::path const &path)
    {
        std::ifstream in(path);
        std::string line;
        std::getline(in, line);
        return line.empty() ? "unknown" : line;
    }

    void pin(std::optional<int> const cpu)
    {
        if (!cpu) {
            return;
        }
        cpu_set_t set;
        CPU_ZERO(&set);
        CPU_SET(*cpu, &set);
        if (sched_setaffinity(0, sizeof set, &set) != 0) {
            die("can't pin to CPU " + std::to_string(*cpu));
        }
    }

    void print_environment(std::optional<int> const cpu)
    {
        std::string model = "unknown";
        std::ifstream cpuinfo("/proc/cpuinfo");
        for (std::string line; std::getline(cpuinfo, line);) {
            if (line.starts_with("model name")) {
                model = line.substr(line.find(':') + 2);
                break;
            }
        }
        std::printf("cpu: %s\n", model.c_str());
        if (cpu) {
            std::string const dir = "/sys/devices/system/cpu/cpu" +
                                    std::to_string(*cpu) + "/cpufreq/";
            std::printf(
                "pinned to cpu %d, governor %s, boost %s\n",
                *cpu,
                first_line(dir + "scaling_governor").c_str(),
                first_line("/sys/devices/system/cpu/cpufreq/boost").c_str());
        }
        else {
            std::printf("not pinned to a cpu: pass --cpu for stable timings\n");
        }
        char const *const tunables = std::getenv("GLIBC_TUNABLES");
        std::printf(
            "GLIBC_TUNABLES: %s\nbuild: %s\n\n",
            tunables ? tunables : "unset",
            MONAD_BENCH_BUILD_TYPE);
        std::fflush(stdout);
    }

    //
    // Graphs
    //

    // A graph, from graph_inputs.py: its graphcode, the code of the accounts
    // its TensorRefs read, a call's inputs, little-endian, dense, and the
    // reference evaluator's outputs, the same, if there are any
    struct GraphCase
    {
        byte_string graphcode;
        std::vector<std::pair<Address, byte_string>> accounts;
        std::vector<byte_string> inputs;
        std::vector<byte_string> expected;
    };

    std::string shell_quote(std::string const &s)
    {
        std::string quoted = "'";
        for (char const c : s) {
            if (c == '\'') {
                quoted += "'\\''";
            }
            else {
                quoted.push_back(c);
            }
        }
        return quoted + "'";
    }

    byte_string parse_hex(std::string_view const hex, std::string const &what)
    {
        auto bytes = from_hex(hex);
        if (!bytes) {
            die("graph_inputs.py gave bad hex for " + what);
        }
        return std::move(*bytes);
    }

    GraphCase read_graph(
        std::filesystem::path const &graph, std::string const &graph_fixture,
        int const call, bool const reference)
    {
        std::string const command =
            "python3 " + shell_quote(MONAD_BENCH_GRAPH_INPUTS) + " " +
            shell_quote(graph_fixture) + " " +
            shell_quote(MONAD_BENCH_REPO_ROOT) + " " +
            shell_quote(graph.string()) + " --call " + std::to_string(call) +
            (reference ? "" : " --no-reference");
        FILE *const pipe = popen(command.c_str(), "r");
        if (!pipe) {
            die("can't run graph_inputs.py");
        }
        std::string output;
        std::array<char, 1 << 16> buffer;
        for (size_t n;
             (n = std::fread(buffer.data(), 1, buffer.size(), pipe));) {
            output.append(buffer.data(), n);
        }
        if (pclose(pipe) != 0) {
            die("graph_inputs.py failed on " + graph.string());
        }

        GraphCase c;
        bool has_graphcode = false;
        std::istringstream lines{output};
        for (std::string line; std::getline(lines, line);) {
            std::istringstream fields{line};
            std::string kind;
            std::string hex;
            fields >> kind;
            if (kind == "graphcode") {
                fields >> hex;
                c.graphcode = parse_hex(hex, kind);
                has_graphcode = true;
            }
            else if (kind == "account") {
                std::string address_hex;
                fields >> address_hex >> hex;
                byte_string const address_bytes =
                    parse_hex(address_hex, "an address");
                if (address_bytes.size() != sizeof(Address::bytes)) {
                    die("graph_inputs.py gave a bad address");
                }
                Address address{};
                std::memcpy(
                    address.bytes, address_bytes.data(), sizeof address.bytes);
                c.accounts.emplace_back(address, parse_hex(hex, kind));
            }
            else if (kind == "input" || kind == "expected") {
                // An empty tensor's hex is empty
                fields >> hex;
                (kind == "input" ? c.inputs : c.expected)
                    .push_back(parse_hex(hex, kind));
            }
        }
        if (!has_graphcode) {
            die("graph_inputs.py gave no graphcode");
        }
        return c;
    }

    // The inputs in evalGraph or evalGraphInto calldata, in the canonical ABI
    // encoding the precompile accepts. Their elements, which may be in the
    // calldata or an account's code, are loaded, in host order
    std::vector<byte_string> read_calldata_inputs(
        byte_string const &calldata, Graphcode const &gc, State &state)
    {
        constexpr uint32_t EVAL_GRAPH = abi_encode_selector(
            "evalGraph(address,(uint8,uint16[],uint8,uint8,bytes)[])");
        constexpr uint32_t EVAL_GRAPH_INTO = abi_encode_selector(
            "evalGraphInto(address,(uint8,uint16[],uint8,uint8,bytes)[],(uint8,"
            "uint8,bytes)[])");
        if (calldata.size() < 4) {
            die("the calldata has no selector");
        }
        uint32_t const selector = static_cast<uint32_t>(calldata[0]) << 24 |
                                  static_cast<uint32_t>(calldata[1]) << 16 |
                                  static_cast<uint32_t>(calldata[2]) << 8 |
                                  static_cast<uint32_t>(calldata[3]);
        if (selector != EVAL_GRAPH && selector != EVAL_GRAPH_INTO) {
            die("the calldata isn't an evalGraph or evalGraphInto call");
        }
        byte_string_view input{calldata};
        input.remove_prefix(4);
        auto const fail = [] { die("the calldata's inputs don't decode"); };

        // The graph's address, then the offsets of the inputs (and outputs)
        if (abi_decode_fixed<Address>(input).has_error()) {
            fail();
        }
        auto const inputs_head = abi_decode_fixed<u256_be>(input);
        size_t const heads = selector == EVAL_GRAPH ? 2 : 3;
        if (heads == 3 && abi_decode_fixed<u256_be>(input).has_error()) {
            fail();
        }
        if (inputs_head.has_error() ||
            inputs_head.value().native() != heads * 32) {
            fail();
        }

        // The inputs' tail: their number, their offsets, then each in turn
        auto const length = abi_decode_fixed<u256_be>(input);
        if (length.has_error() || length.value().native() != gc.n_inputs()) {
            die("the calldata doesn't have the graph's " +
                std::to_string(gc.n_inputs()) + " inputs");
        }
        byte_string_view const elements = input;
        std::vector<uint64_t> offsets;
        for (size_t i = 0; i < gc.n_inputs(); i++) {
            auto const offset = abi_decode_fixed<u256_be>(input);
            if (offset.has_error()) {
                fail();
            }
            offsets.push_back(offset.value().native().as_words()[0]);
        }
        std::vector<byte_string> inputs;
        for (size_t i = 0; i < gc.n_inputs(); i++) {
            if (offsets[i] != elements.size() - input.size()) {
                fail();
            }
            auto const decoded = abi_decode_tensor_input(input);
            if (decoded.has_error()) {
                fail();
            }
            TensorInput const &tensor_input = decoded.value();
            TensorType const &type = gc.tensor_types()[i];
            if (!(tensor_input.type == type)) {
                die("input " + std::to_string(i) +
                    " in the calldata doesn't have the graph's type for it");
            }
            byte_string bytes(type.size_bytes(), 0);
            Tensor tensor{type, bytes.data()};
            if (auto const *const literal =
                    std::get_if<byte_string_view>(&tensor_input.source)) {
                copy_elements(
                    type.dtype(),
                    tensor_input.byte_order,
                    *literal,
                    bytes.data());
            }
            else if (
                auto const *const ref =
                    std::get_if<CodeRef>(&tensor_input.source)) {
                if (load_code_tensor(
                        state, *ref, tensor_input.byte_order, tensor)
                        .has_error()) {
                    die("input " + std::to_string(i) +
                        "'s code reference doesn't hold a tensor of its type");
                }
            }
            else {
                die("input " + std::to_string(i) +
                    " is a storage reference, which needs a caller's storage "
                    "monad-bench doesn't have");
            }
            inputs.push_back(std::move(bytes));
        }
        return inputs;
    }

    struct GraphModes
    {
        bool interpreted = false;
        bool iree = false;
        bool halide = false;
        std::vector<std::string> halide_schedulers;
    };

    struct AlignedFree
    {
        void operator()(uint8_t *const p) const
        {
            std::free(p);
        }
    };

    using AlignedBuffer = std::unique_ptr<uint8_t, AlignedFree>;

    AlignedBuffer aligned_buffer(size_t const size)
    {
        size_t const rounded =
            std::max<size_t>(TENSOR_DATA_ALIGNMENT, (size + 63) / 64 * 64);
        auto *const p = static_cast<uint8_t *>(
            std::aligned_alloc(TENSOR_DATA_ALIGNMENT, rounded));
        MONAD_ASSERT(p);
        return AlignedBuffer{p};
    }

    void bench_graph(
        std::filesystem::path const &path,
        std::optional<std::filesystem::path> const &calldata_path,
        GraphModes const &modes, std::string const &graph_fixture,
        int const call, bool const no_reference, Timing const &timing)
    {
        // The reference evaluator's outputs are for the call's inputs, not
        // the calldata's
        bool const reference = !no_reference && !calldata_path;
        GraphCase const c = read_graph(path, graph_fixture, call, reference);

        // A State whose accounts have the code the graph's TensorRefs read
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm{vm::VM::InterpreterOnly};
        BlockState block_state{tdb, vm};
        State state{block_state, Incarnation{0, 0}};
        for (auto const &[address, code] : c.accounts) {
            state.create_contract(address);
            state.set_code(address, code);
        }

        Graphcode const gc{std::span<uint8_t const>{c.graphcode}};
        if (gc.validation_result() != GraphEvalError::Success) {
            die("the graph doesn't validate");
        }
        std::vector<byte_string> const inputs =
            calldata_path
                ? read_calldata_inputs(read_hex(*calldata_path), gc, state)
                : c.inputs;
        if (inputs.size() != gc.n_inputs()) {
            die("the call doesn't have the graph's inputs");
        }
        auto const output_type = [&](size_t const i) -> TensorType const & {
            return gc.tensor_types()[gc.outputs()[i]];
        };

        auto *const arena = static_cast<uint8_t *>(
            std::aligned_alloc(TENSOR_DATA_ALIGNMENT, ARENA_SIZE));
        MONAD_ASSERT(arena);

        // The interpreter, as run_graph sets it up, from the inputs as
        // literals
        auto const interpret = [&] {
            std::vector<TensorInput> tensor_inputs;
            tensor_inputs.reserve(inputs.size());
            for (size_t i = 0; i < inputs.size(); i++) {
                tensor_inputs.push_back(TensorInput{
                    gc.tensor_types()[i],
                    ByteOrder::LittleEndian,
                    byte_string_view{inputs[i]}});
            }
            Interpreter interpreter{
                state,
                std::move(tensor_inputs),
                nullptr,
                std::nullopt,
                gc,
                arena};
            auto result = interpreter.run();
            if (result.has_error()) {
                die("the interpreter failed: " +
                    std::string{result.error().message().c_str()});
            }
            return std::move(result.value());
        };

        // The outputs to check every mode's against
        std::vector<byte_string> expected = c.expected;
        if (expected.empty()) {
            for (Tensor const &output : interpret()) {
                expected.emplace_back(
                    output.data(), output.type().size_bytes());
            }
        }
        if (expected.size() != gc.outputs().size()) {
            die("the reference evaluator gave the wrong number of outputs");
        }
        std::printf(
            "graph %s: %zu ops, %zu inputs, %zu outputs; outputs checked "
            "against the %s\n\n",
            path.filename().c_str(),
            gc.tensor_types().size() - gc.n_inputs(),
            gc.n_inputs(),
            gc.outputs().size(),
            c.expected.empty() ? "interpreter's" : "reference evaluator's");

        auto const check = [&](std::string const &name, auto const &outputs) {
            for (size_t i = 0; i < expected.size(); i++) {
                byte_string_view const output = outputs(i);
                if (output != byte_string_view{expected[i]}) {
                    die(name + ": output " + std::to_string(i) +
                        " doesn't match the reference");
                }
            }
        };
        print_header();

        if (modes.interpreted) {
            std::vector<Tensor> outputs;
            auto const interpreted_outputs = [&](size_t const i) {
                return byte_string_view{
                    outputs[i].data(), outputs[i].type().size_bytes()};
            };
            outputs = interpret();
            check("interpreted", interpreted_outputs);
            measure(
                "interpreted",
                timing,
                1000,
                [](size_t) {},
                [&](size_t) { interpret(); });
            outputs = interpret();
            check("interpreted", interpreted_outputs);
        }

        // A compiled graph's outputs go at the start of the arena, each
        // aligned, and the rest of it is scratch
        std::vector<uint8_t *> outputs;
        size_t offset = 0;
        for (size_t i = 0; i < gc.outputs().size(); i++) {
            outputs.push_back(arena + offset);
            offset += (output_type(i).size_bytes() + 63) / 64 * 64;
        }
        std::span<uint8_t> const scratch{arena + offset, ARENA_SIZE - offset};
        std::vector<AlignedBuffer> copies;
        std::vector<uint8_t const *> copy_pointers;
        for (auto const &input : inputs) {
            copies.push_back(aligned_buffer(input.size()));
            copy_pointers.push_back(copies.back().get());
        }
        auto const compiled_outputs = [&](size_t const i) {
            return byte_string_view{outputs[i], output_type(i).size_bytes()};
        };
        // Times a compiled graph's `run`, given the copies made in the call
        auto const bench_compiled = [&](std::string const &name, auto &&run) {
            auto const call_once = [&] {
                for (size_t i = 0; i < inputs.size(); i++) {
                    std::memcpy(
                        copies[i].get(), inputs[i].data(), inputs[i].size());
                }
                if (run(copy_pointers, outputs, scratch).has_error()) {
                    die(name + " failed");
                }
            };
            std::memset(arena, 0xa5, offset);
            call_once();
            check(name, compiled_outputs);
            measure(
                name,
                timing,
                1000,
                [](size_t) {},
                [&](size_t) { call_once(); });
            std::memset(arena, 0xa5, offset);
            call_once();
            check(name, compiled_outputs);
        };

        if (modes.iree) {
#ifdef MONAD_BENCH_IREE
            auto const start = Clock::now();
            Compiler compiler{gc, state};
            auto compiled = compiler.compile();
            if (compiled.has_error()) {
                die("IREE couldn't compile the graph: " +
                    std::string{compiled.error().message().c_str()});
            }
            print_compile("iree", elapsed_ns(start));
            bench_compiled(
                "iree", [&](auto const &in, auto const &out, auto s) {
                    return compiled.value().run(in, out, s);
                });
#else
            die("monad-bench was built without IREE (MONAD_GRAPH_EVAL_IREE)");
#endif
        }

        if (modes.halide || !modes.halide_schedulers.empty()) {
#ifdef MONAD_BENCH_HALIDE
            std::vector<std::string> schedules;
            if (modes.halide) {
                schedules.push_back("");
            }
            schedules.insert(
                schedules.end(),
                modes.halide_schedulers.begin(),
                modes.halide_schedulers.end());
            for (std::string const &scheduler : schedules) {
                std::string const name =
                    scheduler.empty() ? "halide" : "halide-" + scheduler;
                auto const start = Clock::now();
                HalideCompiler compiler{gc, state};
                auto compiled =
                    scheduler.empty()
                        ? compiler.compile()
                        : compiler.compile(
                              Halide::AutoschedulerParams{scheduler});
                if (compiled.has_error()) {
                    die("Halide couldn't compile the graph: " +
                        std::string{compiled.error().message().c_str()});
                }
                print_compile(name, elapsed_ns(start));
                bench_compiled(
                    name, [&](auto const &in, auto const &out, auto s) {
                        return compiled.value().run(in, out, s);
                    });
            }
#else
            die("monad-bench was built without Halide "
                "(MONAD_GRAPH_EVAL_HALIDE)");
#endif
        }
        std::free(arena);
    }

    //
    // Bytecode
    //

    struct EvmModes
    {
        bool interpreted = false;
        bool compiled = false;
    };

    // The code, its account's storage, and the call to it
    struct EvmCase
    {
        byte_string code;
        std::vector<std::pair<bytes32_t, bytes32_t>> storage;
        byte_string calldata;
        int64_t gas;
        // The output the calls must return, if given
        std::optional<byte_string> expected;
    };

    // A file of storage slots and their values, a pair a line, in hex, each
    // up to 32 bytes, as numbers; blank lines and lines from a # are ignored
    std::vector<std::pair<bytes32_t, bytes32_t>>
    read_storage(std::filesystem::path const &path)
    {
        auto const word = [&](std::string_view digits) {
            if (digits.starts_with("0x") || digits.starts_with("0X")) {
                digits.remove_prefix(2);
            }
            std::string padded(digits.size() % 2, '0');
            padded += digits;
            auto const bytes = from_hex(padded);
            if (!bytes || bytes->size() > 32) {
                die(path.string() + " has a bad slot or value");
            }
            bytes32_t w{};
            std::memcpy(
                w.bytes + 32 - bytes->size(), bytes->data(), bytes->size());
            return w;
        };
        std::vector<std::pair<bytes32_t, bytes32_t>> storage;
        std::istringstream lines{read_text(path)};
        for (std::string line; std::getline(lines, line);) {
            line = line.substr(0, line.find('#'));
            std::istringstream fields{line};
            std::string slot;
            std::string value;
            if (!(fields >> slot)) {
                continue;
            }
            if (!(fields >> value)) {
                die(path.string() + " has a slot without a value");
            }
            storage.emplace_back(word(slot), word(value));
        }
        return storage;
    }

    // What a call returned, to check every call's against the first's
    struct EvmOutcome
    {
        evmc_status_code status;
        int64_t gas_left;
        int64_t gas_refund;
        byte_string output;

        bool operator==(EvmOutcome const &) const = default;
    };

    EvmOutcome outcome_of(evmc::Result const &result)
    {
        return EvmOutcome{
            result.status_code,
            result.gas_left,
            result.gas_refund,
            byte_string{result.output_data, result.output_size}};
    }

    // A call's output, in hex if it's short, and as its size and hash if not
    std::string describe_output(byte_string const &output)
    {
        if (output.empty()) {
            return "empty";
        }
        if (output.size() <= 64) {
            return "0x" + to_hex(output);
        }
        return std::to_string(output.size()) + " bytes, keccak256 0x" +
               to_hex(to_bytes(keccak256(output)));
    }

    template <Traits traits>
    void
    bench_evm(EvmCase const &c, EvmModes const &modes, Timing const &timing)
    {
        byte_string const &code = c.code;
        byte_string const &calldata = c.calldata;
        int64_t const gas = c.gas;
        std::optional<byte_string> const &expected = c.expected;
        Address const code_address{0xc0de};
        Address const sender_address{0x5e4de4};

        // The code's account, with its storage, and the sender's, set up in
        // a State and committed, as JsonState sets up a test's, which encodes
        // the storage as the revision does
        auto const test_state =
            monad::test::JsonState{}.make_test_state<traits::mip_8_active()>();
        auto const icode = vm::make_shared_intercode(code);
        {
            vm::VM setup_vm;
            BlockState setup{test_state->trie_db, setup_vm};
            State state{setup, Incarnation{0, 0}};
            uint256_t const balance = 1'000'000'000'000'000'000;
            state.create_contract(code_address);
            state.set_code(code_address, code);
            state.add_to_balance(code_address, balance);
            state.set_nonce(code_address, 1);
            for (auto const &[slot, value] : c.storage) {
                if (value != bytes32_t{}) {
                    state.set_storage(code_address, slot, value);
                }
            }
            state.add_to_balance(sender_address, balance);
            state.set_nonce(sender_address, 1);
            setup.merge(state);
            auto [released_state, released_code, _] =
                std::move(setup).release();
            monad::test::commit_simple(
                test_state->trie_db,
                *released_state,
                released_code,
                NULL_HASH_BLAKE3,
                BlockHeader{.number = 1});
        }

        // InterpreterOnly, so that no compile runs in the background
        vm::VM vm{vm::VM::InterpreterOnly};
        BlockState block_state{test_state->trie_db, vm};
        monad::test::TestBlockHashBuffer const block_hash_buffer{};
        Transaction const tx{};
        std::optional<uint256_t> const base_fee_per_gas{};
        std::vector<std::optional<Address>> const authorities{};
        BlockHeader const header{.number = 2};
        MonadDevnet const chain{};

        // A call, in a State of its own, so that each starts from the same
        // state, and with its own message memory
        struct Call
        {
            vm::MemoryPool::Ref memory;
            State state;
            monad::test::TestHost<traits> host;
            evmc_message message;
            vm::runtime::Context context;
            std::optional<evmc::Result> result;

            Call(
                vm::VM &vm, BlockState &block_state,
                BlockHashBuffer const &block_hash_buffer, Transaction const &tx,
                Address const &sender, std::optional<uint256_t> const &base_fee,
                std::vector<std::optional<Address>> const &authorities,
                BlockHeader const &header, Chain const &chain,
                Address const &recipient, byte_string const &calldata,
                byte_string const &code, int64_t const gas)
                : memory{vm.message_memory_ref()}
                , state{block_state, Incarnation{2, 1}}
                , host{block_hash_buffer, state, tx, sender, base_fee, authorities, header, chain}
                , message{
                      .kind = EVMC_CALL,
                      .flags = 0,
                      .depth = 0,
                      .gas = gas,
                      .recipient = recipient,
                      .sender = sender,
                      .input_data = calldata.data(),
                      .input_size = calldata.size(),
                      .value = {},
                      .create2_salt = {},
                      .code_address = recipient,
                      .memory_handle = memory.get(),
                      .memory = memory.get(),
                      .memory_capacity = vm.message_memory_capacity()}
                , context{vm::runtime::Context::from(
                      &host.get_evmc_host().get_interface(),
                      host.get_evmc_host().to_context(),
                      &message,
                      {code.data(), code.size()})}
            {
            }
        };

        std::optional<EvmOutcome> first;
        auto const run_mode =
            [&](std::string const &name,
                vm::compiler::native::entrypoint_t const entrypoint) {
                std::vector<std::unique_ptr<Call>> calls;
                auto const prepare = [&](size_t const n) {
                    calls.clear();
                    for (size_t i = 0; i < n; i++) {
                        calls.push_back(std::make_unique<Call>(
                            vm,
                            block_state,
                            block_hash_buffer,
                            tx,
                            sender_address,
                            base_fee_per_gas,
                            authorities,
                            header,
                            chain,
                            code_address,
                            calldata,
                            code,
                            gas));
                    }
                };
                auto const call = [&](size_t const i) {
                    Call &c = *calls[i];
                    c.result = entrypoint
                                   ? vm.execute_native_entrypoint_raw<traits>(
                                         c.context, entrypoint)
                                   : vm.execute_intercode_raw<traits>(
                                         c.context, icode);
                    c.context.template return_to<traits>(nullptr);
                };
                auto const check = [&] {
                    for (auto const &c : calls) {
                        EvmOutcome const outcome = outcome_of(*c->result);
                        if (!first) {
                            first = outcome;
                            std::printf(
                                "first call: status %d, gas used %lld, refund "
                                "%lld, output %s\n",
                                static_cast<int>(outcome.status),
                                static_cast<long long>(gas - outcome.gas_left),
                                static_cast<long long>(outcome.gas_refund),
                                describe_output(outcome.output).c_str());
                            if (expected) {
                                if (outcome.output != *expected) {
                                    die(name + ": the output isn't --expect's");
                                }
                                std::printf("the output matches --expect's\n");
                            }
                            std::printf("\n");
                            print_header();
                        }
                        else if (outcome != *first) {
                            die(name +
                                ": a call's status, gas or output differs "
                                "from the first call's");
                        }
                    }
                };
                prepare(1);
                call(0);
                check();
                // Each call keeps its message memory, of the VM's message
                // memory capacity, until the next batch, so batches are kept
                // small
                measure(name, timing, 32, prepare, [&](size_t const i) {
                    call(i);
                });
                check();
            };

        if (modes.interpreted) {
            run_mode("interpreted", nullptr);
        }
        if (modes.compiled) {
            auto const start = Clock::now();
            auto const nativecode = vm.compiler().compile<traits>(icode);
            if (!nativecode || !nativecode->entrypoint()) {
                die("the native compiler couldn't compile the bytecode");
            }
            print_compile("compiled", elapsed_ns(start));
            run_mode("compiled", nativecode->entrypoint());
        }
    }

    void bench_evm_at(
        monad_revision const rev, EvmCase const &c, EvmModes const &modes,
        Timing const &timing)
    {
        SWITCH_MONAD_TRAITS(bench_evm, c, modes, timing);
        MONAD_ABORT();
    }

    std::optional<monad_revision> parse_revision(std::string const &name)
    {
        for (int r = MONAD_ZERO; r <= MONAD_NEXT; r++) {
            auto const rev = static_cast<monad_revision>(r);
            if (name == monad_revision_to_string(rev)) {
                return rev;
            }
        }
        return std::nullopt;
    }
}

int main(int argc, char **argv)
{
    CLI::App app{
        "Benchmarks a graph for the graph-eval precompile (.graph), or EVM "
        "runtime bytecode (.bc, hex), with optional calldata (.dat, hex), in "
        "the engines given, on one thread. See cmd/bench/main.cpp for how it "
        "times them."};

    std::filesystem::path input;
    std::optional<std::filesystem::path> calldata;
    bool interpreted = false;
    bool compiled = false;
    GraphModes graph_modes;
    bool mullapudi = false;
    bool adams = false;
    bool li = false;
    std::optional<int> cpu;
    Timing timing;
    std::string revision_name = monad_revision_to_string(MONAD_TEN);
    int64_t gas = 30'000'000;
    int call = 0;
    bool no_reference = false;
    std::optional<std::filesystem::path> expect;
    std::optional<std::filesystem::path> storage;
    std::string graph_fixture = MONAD_BENCH_GRAPH_FIXTURE;

    app.add_option(
           "input", input, "A .graph file, or a .bc file of bytecode in hex")
        ->required()
        ->check(CLI::ExistingFile);
    app.add_option("calldata", calldata, "A .dat file of calldata in hex")
        ->check(CLI::ExistingFile);

    app.add_flag("--interpreted", interpreted, "Run in the interpreter");
    app.add_flag(
        "--compiled", compiled, "Bytecode: run compiled to native code");
    app.add_flag("--iree", graph_modes.iree, "Graph: run compiled with IREE");
    app.add_flag(
        "--halide",
        graph_modes.halide,
        "Graph: run compiled with Halide, with the hand-written schedule");
    app.add_flag(
        "--halide-mullapudi2016",
        mullapudi,
        "Graph: run compiled with Halide, scheduled by Mullapudi2016");
    app.add_flag(
        "--halide-adams2019",
        adams,
        "Graph: run compiled with Halide, scheduled by Adams2019");
    app.add_flag(
        "--halide-li2018",
        li,
        "Graph: run compiled with Halide, scheduled by Li2018");

    app.add_option("--cpu", cpu, "Pin to this CPU");
    app.add_option("--time", timing.seconds, "Seconds to time each mode for")
        ->capture_default_str();
    app.add_option(
           "--warmup", timing.warmup, "Seconds to warm each mode up for")
        ->capture_default_str();
    app.add_option(
           "--min-batches", timing.min_batches, "Fewest batches to time")
        ->capture_default_str();
    app.add_option("--revision", revision_name, "Bytecode: the Monad revision")
        ->capture_default_str();
    app.add_option("--gas", gas, "Bytecode: the call's gas")
        ->capture_default_str();
    app.add_option(
           "--storage",
           storage,
           "Bytecode: a file of the code's storage, a slot and its value a "
           "line, in hex")
        ->check(CLI::ExistingFile);
    app.add_option(
           "--expect",
           expect,
           "Bytecode: a file of the output the calls must return, in hex")
        ->check(CLI::ExistingFile);
    app.add_option("--call", call, "Graph: the call whose inputs to use")
        ->capture_default_str();
    app.add_flag(
        "--no-reference",
        no_reference,
        "Graph: check outputs against the interpreter's rather than the "
        "reference evaluator's, which is slow for large graphs");
    app.add_option(
           "--graph-fixture",
           graph_fixture,
           "Graph: graph_fixture.py, which parses .graph files")
        ->capture_default_str();

    CLI11_PARSE(app, argc, argv);

    if (mullapudi) {
        graph_modes.halide_schedulers.push_back("Mullapudi2016");
    }
    if (adams) {
        graph_modes.halide_schedulers.push_back("Adams2019");
    }
    if (li) {
        graph_modes.halide_schedulers.push_back("Li2018");
    }
    graph_modes.interpreted = interpreted;

    pin(cpu);
    std::string const extension = input.extension().string();
    if (calldata && calldata->extension() != ".dat") {
        die("calldata must be a .dat file");
    }
    if (extension == ".bc") {
        if (graph_modes.iree || graph_modes.halide ||
            !graph_modes.halide_schedulers.empty()) {
            die("--iree and --halide* are for .graph files");
        }
        if (!interpreted && !compiled) {
            die("give --interpreted, --compiled, or both");
        }
        auto const rev = parse_revision(revision_name);
        if (!rev) {
            die("no Monad revision " + revision_name);
        }
        EvmCase const c{
            .code = read_hex(input),
            .storage = storage ? read_storage(*storage)
                               : std::vector<std::pair<bytes32_t, bytes32_t>>{},
            .calldata = calldata ? read_hex(*calldata) : byte_string{},
            .gas = gas,
            .expected =
                expect ? std::optional{read_hex(*expect)} : std::nullopt};
        print_environment(cpu);
        std::printf(
            "bytecode %s: %zu bytes, %zu storage slots, calldata %zu bytes, "
            "%s, gas %lld\n",
            input.filename().c_str(),
            c.code.size(),
            c.storage.size(),
            c.calldata.size(),
            revision_name.c_str(),
            static_cast<long long>(gas));
        bench_evm_at(*rev, c, EvmModes{interpreted, compiled}, timing);
    }
    else if (extension == ".graph") {
        if (compiled) {
            die("--compiled is for .bc files; give --iree or --halide*");
        }
        if (!interpreted && !graph_modes.iree && !graph_modes.halide &&
            graph_modes.halide_schedulers.empty()) {
            die("give one or more of --interpreted, --iree, --halide*");
        }
        print_environment(cpu);
        bench_graph(
            input,
            calldata,
            graph_modes,
            graph_fixture,
            call,
            no_reference,
            timing);
    }
    else {
        die("the input must be a .graph or .bc file");
    }
    return 0;
}
