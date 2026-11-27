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
//     monad-bench <file.gc | file.bc> [file.dat] <modes...> [options]
//
// A .gc file is a graph's graphcode, as scripts/graphcode.py
// writes it, a .bc file EVM runtime bytecode, and a
// .dat file calldata, all in hex, where whitespace and a leading 0x are
// ignored. Bytecode runs in the monad
// VM's interpreter (--interpreted) or its native compiler (--compiled), as the
// code of an account, with the storage in --storage's file, that a sender
// calls with the calldata, under a Monad revision (--revision), with the other
// accounts in --accounts' file, an address and its code in hex a line. With
// --deploy, the .bc file is creation code, with any constructor arguments
// appended: it runs once, interpreted, and the code it returns is the code the
// calls run. Each call starts from the same state, in a State of its own.
// Calls the code makes to other accounts are interpreted in both modes.
//
// A graph runs on the inputs in the evalGraph calldata in a
// .dat file, which it needs, with the accounts in --accounts' file, an address
// and its code in hex a line, for the code its TensorRefs and the calldata's
// code references read. The graph runs in the interpreter (--interpreted)
// or the fast interpreter (--fast). Each call is timed from the inputs,
// decoded, in memory, to the outputs written, in the same way for each engine:
// it copies the inputs into its arena, as the precompile does.
//
// Each mode's results are checked before and after it's timed: a graph's
// outputs against the interpreter's, and bytecode's status, gas and output
// against the first call's, and its output against the one in --expect's
// file, if given. Each mode is timed in batches of calls of about a
// millisecond, after a warm-up, for a set time, and the time per call is
// reported as the minimum, median, 90th percentile and maximum over the
// batches. Compiling is timed apart, once.

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
#include <category/execution/monad/graph_eval/fast_interpreter.hpp>
#include <category/execution/monad/graph_eval/graphcode.hpp>
#include <category/execution/monad/graph_eval/interpreter.hpp>
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

#include <CLI/CLI.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <sched.h>

#include <algorithm>
#include <array>
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

    // The accounts in an --accounts file: an address and its code, in hex, a
    // line. `#` starts a comment, and an address alone has no code
    std::vector<std::pair<Address, byte_string>>
    read_accounts(std::filesystem::path const &path)
    {
        auto const bytes = [&](std::string_view digits) {
            if (digits.starts_with("0x") || digits.starts_with("0X")) {
                digits.remove_prefix(2);
            }
            auto parsed = from_hex(digits);
            if (!parsed) {
                die(path.string() + " has an address or code that isn't hex");
            }
            return std::move(*parsed);
        };
        std::vector<std::pair<Address, byte_string>> accounts;
        std::istringstream lines{read_text(path)};
        for (std::string line; std::getline(lines, line);) {
            line = line.substr(0, line.find('#'));
            std::istringstream fields{line};
            std::string address_hex;
            std::string code_hex;
            if (!(fields >> address_hex)) {
                continue;
            }
            fields >> code_hex;
            byte_string const address_bytes = bytes(address_hex);
            if (address_bytes.size() != sizeof(Address::bytes)) {
                die(path.string() + " has an address that isn't 20 bytes");
            }
            Address address{};
            std::memcpy(
                address.bytes, address_bytes.data(), sizeof address.bytes);
            accounts.emplace_back(address, bytes(code_hex));
        }
        return accounts;
    }

    // The inputs in evalGraph calldata, in the canonical ABI encoding the
    // precompile accepts, decoded as the precompile decodes them: a literal's
    // elements stay in place in `calldata`, big-endian, and a code reference
    // stays a reference
    std::vector<TensorInput>
    read_calldata_inputs(byte_string const &calldata, Graphcode const &fc)
    {
        constexpr uint32_t EVAL_GRAPH = abi_encode_selector(
            "evalGraph(address,((uint8,uint16[]),uint8,bytes)[])");
        if (calldata.size() < 4) {
            die("the calldata has no selector");
        }
        uint32_t const selector = static_cast<uint32_t>(calldata[0]) << 24 |
                                  static_cast<uint32_t>(calldata[1]) << 16 |
                                  static_cast<uint32_t>(calldata[2]) << 8 |
                                  static_cast<uint32_t>(calldata[3]);
        if (selector != EVAL_GRAPH) {
            die("the calldata isn't an evalGraph call");
        }
        byte_string_view input{calldata};
        input.remove_prefix(4);
        auto const fail = [] { die("the calldata's inputs don't decode"); };

        // The graph's address, then the offset of the inputs
        if (abi_decode_fixed<Address>(input).has_error()) {
            fail();
        }
        auto const inputs_head = abi_decode_fixed<u256_be>(input);
        if (inputs_head.has_error() || inputs_head.value().native() != 2 * 32) {
            fail();
        }

        // The inputs' tail: their number, their offsets, then each in turn
        auto const length = abi_decode_fixed<u256_be>(input);
        if (length.has_error() || length.value().native() != fc.n_inputs()) {
            die("the calldata doesn't have the graph's " +
                std::to_string(fc.n_inputs()) + " inputs");
        }
        byte_string_view const elements = input;
        std::vector<uint64_t> offsets;
        for (size_t i = 0; i < fc.n_inputs(); i++) {
            auto const offset = abi_decode_fixed<u256_be>(input);
            if (offset.has_error()) {
                fail();
            }
            offsets.push_back(offset.value().native().as_words()[0]);
        }
        std::vector<TensorInput> inputs;
        for (size_t i = 0; i < fc.n_inputs(); i++) {
            if (offsets[i] != elements.size() - input.size()) {
                fail();
            }
            auto const decoded = abi_decode_tensor_input(input);
            if (decoded.has_error()) {
                fail();
            }
            TensorInput const &tensor_input = decoded.value();
            if (!(tensor_input.type == fc.node_type(i))) {
                die("input " + std::to_string(i) +
                    " in the calldata doesn't have the graph's type for it");
            }
            inputs.push_back(tensor_input);
        }
        return inputs;
    }

    struct GraphModes
    {
        // The interpreter
        bool interpreted = false;
        // The fast interpreter
        bool fast = false;
    };

    void bench_graph(
        std::filesystem::path const &path,
        std::filesystem::path const &calldata_path,
        std::optional<std::filesystem::path> const &accounts_path,
        GraphModes const &modes, Timing const &timing)
    {
        byte_string const graphcode = read_hex(path);

        // A State whose accounts have the code the graph's TensorRefs, and
        // the calldata's code references, read
        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm{vm::VM::InterpreterOnly};
        BlockState block_state{tdb, vm};
        State state{block_state, Incarnation{0, 0}};
        if (accounts_path) {
            for (auto const &[address, code] : read_accounts(*accounts_path)) {
                state.create_contract(address);
                state.set_code(address, code);
            }
        }

        // Validated once, outside the timing, as the precompile's Intercode
        // validates a graph once
        Graphcode const fc =
            graph_eval::validate(std::span<uint8_t const>{graphcode});
        if (fc.validation_result() != GraphEvalError::Success) {
            die("the graph doesn't validate");
        }
        // The inputs as run_graph is given them, already decoded. Their
        // literals point into `calldata`
        byte_string const calldata = read_hex(calldata_path);
        std::vector<TensorInput> const tensor_inputs =
            read_calldata_inputs(calldata, fc);

        auto *const arena = static_cast<uint8_t *>(
            std::aligned_alloc(TENSOR_DATA_ALIGNMENT, ARENA_SIZE));
        MONAD_ASSERT(arena);

        // One call in an interpreter, Interpreter or
        // FastInterpreter, which copies the inputs into its arena
        auto const run = [&]<typename Engine>(std::string const &name) {
            Engine engine{fc, state, tensor_inputs, arena};
            auto result = engine.run();
            if (result.has_error()) {
                die(name + " failed: " +
                    std::string{result.error().message().c_str()});
            }
            return std::move(result.value());
        };

        // The outputs to check every mode's against: the interpreter's
        std::vector<byte_string> expected;
        for (Tensor const &output :
             run.template operator()<Interpreter>("interpreted")) {
            expected.emplace_back(output.data(), output.type().size_bytes());
        }
        std::printf(
            "graph %s: %zu ops, %zu inputs, %zu outputs; outputs checked "
            "against the interpreter's\n\n",
            path.filename().c_str(),
            fc.n_ops(),
            fc.n_inputs(),
            fc.output_ids().size());

        auto const check = [&](std::string const &name,
                               GraphOutputs const &outputs) {
            for (size_t i = 0; i < expected.size(); i++) {
                byte_string_view const output{
                    outputs[i].data(), outputs[i].type().size_bytes()};
                if (output != byte_string_view{expected[i]}) {
                    die(name + ": output " + std::to_string(i) +
                        " doesn't match the interpreter's");
                }
            }
        };
        print_header();

        // A mode's outputs are checked before and after it's timed, each time
        // from an arena filled with a pattern, so that an output it doesn't
        // write is caught
        auto const bench = [&]<typename Engine>(std::string const &name) {
            std::memset(arena, 0xa5, ARENA_SIZE);
            check(name, run.template operator()<Engine>(name));
            measure(
                name,
                timing,
                1000,
                [](size_t) {},
                [&](size_t) { run.template operator()<Engine>(name); });
            std::memset(arena, 0xa5, ARENA_SIZE);
            check(name, run.template operator()<Engine>(name));
        };
        if (modes.interpreted) {
            bench.template operator()<Interpreter>("interpreted");
        }
        if (modes.fast) {
            bench.template operator()<FastInterpreter>("fast");
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
        // The code the calls run, or with `deploy`, the creation code, with
        // any constructor arguments, whose output is that code
        byte_string code;
        bool deploy;
        std::vector<std::pair<bytes32_t, bytes32_t>> storage;
        // Other accounts and their code, which the code can read
        std::vector<std::pair<Address, byte_string>> accounts;
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

    Address const EVM_CODE_ADDRESS{0xc0de};
    Address const EVM_SENDER_ADDRESS{0x5e4de4};

    // The code's account, with its storage, the case's other accounts, and
    // the sender's, set up in a State and committed, as JsonState sets up a
    // test's, which encodes the storage as the revision does
    template <Traits traits>
    auto evm_test_state(EvmCase const &c, byte_string const &code)
    {
        auto test_state =
            monad::test::JsonState{}.make_test_state<traits::mip_8_active()>();
        vm::VM setup_vm;
        BlockState setup{test_state->trie_db, setup_vm};
        State state{setup, Incarnation{0, 0}};
        uint256_t const balance = 1'000'000'000'000'000'000;
        state.create_contract(EVM_CODE_ADDRESS);
        state.set_code(EVM_CODE_ADDRESS, code);
        state.add_to_balance(EVM_CODE_ADDRESS, balance);
        state.set_nonce(EVM_CODE_ADDRESS, 1);
        for (auto const &[slot, value] : c.storage) {
            if (value != bytes32_t{}) {
                state.set_storage(EVM_CODE_ADDRESS, slot, value);
            }
        }
        for (auto const &[address, account_code] : c.accounts) {
            state.create_contract(address);
            state.set_code(address, account_code);
            state.set_nonce(address, 1);
        }
        state.add_to_balance(EVM_SENDER_ADDRESS, balance);
        state.set_nonce(EVM_SENDER_ADDRESS, 1);
        setup.merge(state);
        auto [released_state, released_code, _] = std::move(setup).release();
        monad::test::commit_simple(
            test_state->trie_db,
            *released_state,
            released_code,
            NULL_HASH_BLAKE3,
            BlockHeader{.number = 1});
        return test_state;
    }

    // A call to the code's account, in a State of its own, so that each
    // starts from the same state, and with its own message memory
    template <Traits traits>
    struct EvmCall
    {
        vm::MemoryPool::Ref memory;
        State state;
        monad::test::TestHost<traits> host;
        evmc_message message;
        vm::runtime::Context context;
        std::optional<evmc::Result> result;

        EvmCall(
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

    // The code the creation code in `c` returns: run once, interpreted, as
    // the code of the code's account, with no calldata, so that constructor
    // arguments appended to it are read with CODECOPY, as in a CREATE, and
    // the case's other accounts in place. Fails unless it succeeds
    template <Traits traits>
    byte_string deploy_code(EvmCase const &c)
    {
        auto const test_state = evm_test_state<traits>(c, c.code);
        auto const icode = vm::make_shared_intercode(c.code);
        vm::VM vm{vm::VM::InterpreterOnly};
        BlockState block_state{test_state->trie_db, vm};
        monad::test::TestBlockHashBuffer const block_hash_buffer{};
        Transaction const tx{};
        MonadDevnet const chain{};
        byte_string const no_calldata;
        EvmCall<traits> call{
            vm,
            block_state,
            block_hash_buffer,
            tx,
            EVM_SENDER_ADDRESS,
            std::nullopt,
            {},
            BlockHeader{.number = 2},
            chain,
            EVM_CODE_ADDRESS,
            no_calldata,
            c.code,
            c.gas};
        call.result = vm.execute_intercode_raw<traits>(call.context, icode);
        call.context.template return_to<traits>(nullptr);
        if (call.result->status_code != EVMC_SUCCESS) {
            die(std::format(
                "the creation code failed, with status {}",
                static_cast<int>(call.result->status_code)));
        }
        byte_string code{call.result->output_data, call.result->output_size};
        std::printf(
            "deployed: the creation code returned %zu bytes of code, using "
            "%lld gas\n",
            code.size(),
            static_cast<long long>(c.gas - call.result->gas_left));
        return code;
    }

    template <Traits traits>
    void
    bench_evm(EvmCase const &c, EvmModes const &modes, Timing const &timing)
    {
        byte_string const code = c.deploy ? deploy_code<traits>(c) : c.code;
        byte_string const &calldata = c.calldata;
        int64_t const gas = c.gas;
        std::optional<byte_string> const &expected = c.expected;
        Address const &code_address = EVM_CODE_ADDRESS;
        Address const &sender_address = EVM_SENDER_ADDRESS;

        auto const test_state = evm_test_state<traits>(c, code);
        auto const icode = vm::make_shared_intercode(code);

        // InterpreterOnly, so that no compile runs in the background
        vm::VM vm{vm::VM::InterpreterOnly};
        BlockState block_state{test_state->trie_db, vm};
        monad::test::TestBlockHashBuffer const block_hash_buffer{};
        Transaction const tx{};
        std::optional<uint256_t> const base_fee_per_gas{};
        std::vector<std::optional<Address>> const authorities{};
        BlockHeader const header{.number = 2};
        MonadDevnet const chain{};
        using Call = EvmCall<traits>;

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
        "Benchmarks a graph for the graph-eval precompile (.gc, graphcode in "
        "hex) with calldata (.dat, hex), or EVM runtime bytecode (.bc, hex) "
        "with optional calldata, in the engines given, on one thread. See "
        "cmd/bench/main.cpp for how it times them."};

    std::filesystem::path input;
    std::optional<std::filesystem::path> calldata;
    bool interpreted = false;
    bool compiled = false;
    GraphModes graph_modes;
    std::optional<int> cpu;
    Timing timing;
    std::string revision_name = monad_revision_to_string(MONAD_TEN);
    int64_t gas = 30'000'000;
    std::optional<std::filesystem::path> expect;
    std::optional<std::filesystem::path> storage;
    std::optional<std::filesystem::path> accounts;
    bool deploy = false;

    app.add_option(
           "input",
           input,
           "A .gc file of graphcode in hex, or a .bc file of bytecode in hex")
        ->required()
        ->check(CLI::ExistingFile);
    app.add_option(
           "calldata",
           calldata,
           "A .dat file of calldata in hex; a graph's evalGraph call")
        ->check(CLI::ExistingFile);

    app.add_flag("--interpreted", interpreted, "Run in the interpreter");
    app.add_flag(
        "--compiled", compiled, "Bytecode: run compiled to native code");
    app.add_flag(
        "--fast",
        graph_modes.fast,
        "Graph: run in the fast interpreter, whose Scalar fns are "
        "chained by tail calls");

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
    app.add_option(
           "--accounts",
           accounts,
           "A file of accounts and their code, an address and its code a "
           "line, in hex: for a graph, the code its TensorRefs, or the "
           "calldata's code references, read; for bytecode, other accounts "
           "the code reads, as with EXTCODECOPY")
        ->check(CLI::ExistingFile);
    app.add_flag(
        "--deploy",
        deploy,
        "Bytecode: the .bc file is creation code, with any constructor "
        "arguments appended; it runs once, interpreted, and the code it "
        "returns is the code the calls run");

    CLI11_PARSE(app, argc, argv);

    graph_modes.interpreted = interpreted;

    pin(cpu);
    std::string const extension = input.extension().string();
    if (calldata && calldata->extension() != ".dat") {
        die("calldata must be a .dat file");
    }
    if (extension == ".bc") {
        if (graph_modes.fast) {
            die("--fast is for .gc files");
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
            .deploy = deploy,
            .storage = storage ? read_storage(*storage)
                               : std::vector<std::pair<bytes32_t, bytes32_t>>{},
            .accounts = accounts
                            ? read_accounts(*accounts)
                            : std::vector<std::pair<Address, byte_string>>{},
            .calldata = calldata ? read_hex(*calldata) : byte_string{},
            .gas = gas,
            .expected =
                expect ? std::optional{read_hex(*expect)} : std::nullopt};
        print_environment(cpu);
        std::printf(
            "bytecode %s: %zu bytes%s, %zu storage slots, %zu other "
            "accounts, calldata %zu bytes, %s, gas %lld\n",
            input.filename().c_str(),
            c.code.size(),
            deploy ? " of creation code" : "",
            c.storage.size(),
            c.accounts.size(),
            c.calldata.size(),
            revision_name.c_str(),
            static_cast<long long>(gas));
        bench_evm_at(*rev, c, EvmModes{interpreted, compiled}, timing);
    }
    else if (extension == ".gc") {
        if (!calldata) {
            die("a .gc file needs a .dat file of calldata for its inputs");
        }
        if (compiled) {
            die("--compiled is for .bc files; give --interpreted, --fast or "
                "both");
        }
        if (!interpreted && !graph_modes.fast) {
            die("give --interpreted, --fast, or both");
        }
        print_environment(cpu);
        bench_graph(input, *calldata, accounts, graph_modes, timing);
    }
    else {
        die("the input must be a .gc or .bc file");
    }
    return 0;
}
