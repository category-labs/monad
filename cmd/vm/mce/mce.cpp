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

#include <instrumentable_compiler.hpp>
#include <instrumentable_decoder.hpp>
#include <instrumentable_parser.hpp>
#include <instrumentable_vm.hpp>
#include <instrumentation_device.hpp>
#include <operands_logger.cpp>
#include <stopwatch.hpp>

#include <category/core/runtime/uint256.hpp>
#include <category/vm/compiler/ir/basic_blocks.hpp>
#include <category/vm/compiler/ir/x86/types.hpp>
#include <category/vm/compiler/types.hpp>
#include <category/vm/evm/traits.hpp>

#include <asmjit/core/jitruntime.h>

#include <CLI/CLI.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <format>
#include <ios>
#include <iostream>
#include <memory>
#include <optional>
#include <ostream>
#include <string>
#include <vector>

using namespace monad::vm;

struct arguments
{
    std::string filename;
    std::string revision = "latest";
    std::string timeunit_s = "ns";
    Timeunit timeunit = Timeunit::nano;
    bool instrument_decode = false;
    bool instrument_parse = false;
    bool instrument_compile = false;
    bool instrument_execute = false;
    bool instrument_compile_operands = false;
    bool compile_only = false;
    std::optional<std::string> asm_log_file;
    bool wall_clock_time = false;
    bool report_result = false;
};

static arguments parse_args(int const argc, char **const argv)
{
    auto app =
        CLI::App("Instrumentable standalone monad compiler execution engine");
    auto args = arguments{};

    app.add_option("filename", args.filename, "File to compile and execute");
    app.add_option(
        "--rev",
        args.revision,
        std::format("Set EVM revision (default: {})", args.revision));
    app.add_flag(
        "-d",
        args.instrument_decode,
        std::format(
            "Instrument decoding (default: {})", args.instrument_decode));
    app.add_flag(
        "-p",
        args.instrument_parse,
        std::format("Instrument parsing (default: {})", args.instrument_parse));
    app.add_flag(
        "-c",
        args.instrument_compile,
        std::format(
            "Instrument compilation (default: {})", args.instrument_compile));
    app.add_flag(
        "-e",
        args.instrument_execute,
        std::format(
            "Instrument execution (default: {})", args.instrument_execute));
    app.add_flag(
        "-o",
        args.instrument_compile_operands,
        std::format(
            "Instrument compilation of operands (default: {})",
            args.instrument_compile_operands));
    app.add_flag(
        "--compile-only",
        args.compile_only,
        "Parse bytecode and compile only, skip execution");
    app.add_option(
        "--dump-asm", args.asm_log_file, "Dump assembly output to file");
    app.add_flag(
        "-r",
        args.report_result,
        std::format(
            "Report execution result (default: {})", args.report_result));
    app.add_flag(
        "-w",
        args.wall_clock_time,
        std::format(
            "Report wall clock time (default: {})", args.wall_clock_time));
    app.add_option(
        "-u",
        args.timeunit_s,
        std::format("Wall clock time unit (default: {})", args.timeunit_s));

    try {
        app.parse(argc, argv);
        args.timeunit = timeunit_of_short_string(args.timeunit_s);
        if (args.filename.empty()) {
            throw CLI::ParseError{"filename: no input file", 105};
        }
    }
    catch (CLI::ParseError const &e) {
        std::exit(app.exit(e));
    }

    return args;
}

static void dump_result(arguments const &args, evmc::Result const &result)
{
    if (!args.report_result && !args.wall_clock_time) {
        // Nothing to report.
        return;
    }

    using json = nlohmann::json;

    json object{};
    if (args.wall_clock_time) {
        json time{};
        time["elapsed"] = json(timer.elapsed_formatted_string(args.timeunit));
        time["unit"] = json(short_string_of_timeunit(args.timeunit));
        object["time"] = time;
    }

    if (result.status_code == EVMC_SUCCESS) {
        if (result.output_size == 0) {
            object["result"] = json("");
        }
        else {
            auto const x = uint256_t::load_be_unsafe(&result.output_data[0]);
            object["result"] = json(x.to_string(16));
        }
    }
    else {
        switch (result.status_code) {
        case EVMC_FAILURE:
            object["error"] = json("failure");
            break;
        case EVMC_INTERNAL_ERROR:
            object["error"] = json("internal error");
            break;
        case EVMC_OUT_OF_GAS:
            object["error"] = json("out of gas");
            break;
        case EVMC_STACK_OVERFLOW:
            object["error"] = json("stack overflow");
            break;
        case EVMC_STACK_UNDERFLOW:
            object["error"] = json("stack underflow");
            break;
        default:
            object["error"] = json("unknown failure");
        }
    }
    std::cout << object.dump(2) << std::endl;
}

template <Traits traits>
int mce_main(arguments const &args)
{
    auto const device = args.wall_clock_time
                            ? InstrumentationDevice::WallClock
                            : InstrumentationDevice::Cachegrind;
    std::vector<uint8_t> const bytes = [&]() {
        if (args.instrument_decode) {
            InstrumentableDecoder<true> decoder{};
            return decoder.decode(args.filename, device);
        }
        else {
            InstrumentableDecoder<false> decoder{};
            return decoder.decode(args.filename, device);
        }
    }();

    std::optional<basic_blocks::BasicBlocksIR> const ir = [&]() {
        if (args.instrument_parse) {
            InstrumentableParser<true> parser{};
            return parser.parse<traits>(bytes, device);
        }
        else {
            InstrumentableParser<false> parser{};
            return parser.parse<traits>(bytes, device);
        }
    }();
    if (!ir) {
        std::cerr << "Parsing failed" << std::endl;
        return 1;
    }

    asmjit::JitRuntime rt{};
    native::CompilerConfig config{};
    OperandsLoggerState operands_logger_state(ir->blocks().size());

    if (args.asm_log_file) {
        config.asm_log_path = args.asm_log_file->c_str();
    }
    if (args.instrument_compile_operands) {
        // This will log the operands of each instruction
        std::tie(config.pre_instruction_emit_hook, config.post_instruction_emit_hook) =
            operands_logger_make_hooks(operands_logger_state);
    }
    std::shared_ptr<native::Nativecode> const ncode = [&]() {
        if (args.instrument_compile) {
            InstrumentableCompiler<true> compiler(rt, config);
            return compiler.compile<traits>(*ir, device);
        }
        else {
            InstrumentableCompiler<false> compiler(rt, config);
            return compiler.compile<traits>(*ir, device);
        }
    }();

    if (!ncode->entrypoint()) {
        std::cerr << "Compilation failed" << std::endl;
        return 1;
    }

    if (args.instrument_compile_operands) {
        std::cout << operands_logger_state.to_json(ir.value()).dump() << std::endl;
    }

    if (!args.compile_only) {
        evmc::Result const result = [&]() {
            if (args.instrument_execute) {
                InstrumentableVM<true> vm(rt);
                return vm.execute<traits>(ncode->entrypoint(), device);
            }
            else {
                InstrumentableVM<false> vm(rt);
                return vm.execute<traits>(ncode->entrypoint(), device);
            }
        }();

        dump_result(args, result);

        auto status_code = result.status_code;

        return status_code == EVMC_SUCCESS ? 0 : 1;
    }
    else {
        return 0;
    }
}

static std::string uppercase(std::string s)
{
    std::transform(s.begin(), s.end(), s.begin(), [](unsigned char c) {
        return std::toupper(c);
    });
    return s;
}

int main(int argc, char **argv)
{
    std::ios_base::sync_with_stdio(false);
    auto args = parse_args(argc, argv);
    std::string const rev = uppercase(args.revision);
    if (rev == "FRONTIER") {
        return mce_main<EvmTraits<EVMC_FRONTIER>>(args);
    }
    else if (rev == "HOMESTEAD") {
        return mce_main<EvmTraits<EVMC_HOMESTEAD>>(args);
    }
    else if (rev == "TANGERINE_WHISTLE") {
        return mce_main<EvmTraits<EVMC_TANGERINE_WHISTLE>>(args);
    }
    else if (rev == "SPURIOUS_DRAGON") {
        return mce_main<EvmTraits<EVMC_SPURIOUS_DRAGON>>(args);
    }
    else if (rev == "BYZANTIUM") {
        return mce_main<EvmTraits<EVMC_BYZANTIUM>>(args);
    }
    else if (rev == "CONSTANTINOPLE") {
        return mce_main<EvmTraits<EVMC_CONSTANTINOPLE>>(args);
    }
    else if (rev == "PETERSBURG") {
        return mce_main<EvmTraits<EVMC_PETERSBURG>>(args);
    }
    else if (rev == "ISTANBUL") {
        return mce_main<EvmTraits<EVMC_ISTANBUL>>(args);
    }
    else if (rev == "BERLIN") {
        return mce_main<EvmTraits<EVMC_BERLIN>>(args);
    }
    else if (rev == "LONDON") {
        return mce_main<EvmTraits<EVMC_LONDON>>(args);
    }
    else if (rev == "PARIS") {
        return mce_main<EvmTraits<EVMC_PARIS>>(args);
    }
    else if (rev == "SHANGHAI") {
        return mce_main<EvmTraits<EVMC_SHANGHAI>>(args);
    }
    else if (rev == "CANCUN") {
        return mce_main<EvmTraits<EVMC_CANCUN>>(args);
    }
    else if (rev == "PRAGUE") {
        return mce_main<EvmTraits<EVMC_PRAGUE>>(args);
    }
    else if (rev == "OSAKA") {
        return mce_main<EvmTraits<EVMC_OSAKA>>(args);
    }
    else if (rev == "LATEST") {
        return mce_main<EvmTraits<EVMC_LATEST_STABLE_REVISION>>(args);
    }
    else {
        std::cerr << std::format(
                         "error: unsupported revision '{}'", args.revision)
                  << std::endl;
        return 1;
    }
}
