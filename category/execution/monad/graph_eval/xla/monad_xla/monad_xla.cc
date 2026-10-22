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

// libmonad_xla.so's implementation, built by Bazel in XLA's workspace; see
// monad_xla.h. It compiles as NanoRtClient::Compile does
// (xla/backends/cpu/nanort/nanort_client.cc), but with options of its own
// rather than XLA_FLAGS's, which aborts the process on a flag it doesn't know

#include "monad_xla/monad_xla.h"

#include <cstddef>
#include <cstdlib>
#include <cstring>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "absl/container/inlined_vector.h"
#include "absl/status/status.h"
#include "absl/status/statusor.h"
#include "absl/strings/str_cat.h"
#include "absl/strings/string_view.h"
#include "absl/types/span.h"
#include "xla/backends/cpu/nanort/nanort_executable.h"
#include "xla/backends/cpu/target_machine_options.h"
#include "xla/debug_options_flags.h"
#include "xla/hlo/ir/hlo_module.h"
#include "xla/hlo/parser/hlo_parser.h"
#include "xla/layout_util.h"
#include "xla/service/compiler.h"
#include "xla/service/cpu/cpu_compiler.h"
#include "xla/service/executable.h"
#include "xla/service/hlo_module_config.h"
#include "xla/shape.h"
#include "xla/shape_util.h"
#include "xla/xla.pb.h"

struct monad_xla_executable
{
    std::unique_ptr<xla::cpu::NanoRtExecutable> nanort;
    std::vector<size_t> parameter_sizes;
    std::vector<size_t> result_sizes;
    size_t temp_size;
};

namespace
{
    char *copy_string(std::string const &s)
    {
        char *const copy = static_cast<char *>(std::malloc(s.size() + 1));
        if (copy) {
            std::memcpy(copy, s.c_str(), s.size() + 1);
        }
        return copy;
    }

    monad_xla_status
    fail(monad_xla_status const status, absl::Status const &error, char **out)
    {
        if (out) {
            *out = copy_string(std::string(error.message()));
        }
        return status;
    }

    // The bytes of an array in the default layout, which is the only one
    // monad_xla_run's callers lay arrays out in
    absl::StatusOr<size_t> array_size(xla::Shape const &shape)
    {
        if (!shape.IsArray()) {
            return absl::InvalidArgumentError(
                absl::StrCat("not an array: ", shape.ToString()));
        }
        if (shape.has_layout() &&
            !xla::LayoutUtil::IsMonotonicWithDim0Major(shape.layout())) {
            return absl::InvalidArgumentError(
                absl::StrCat("not row-major: ", shape.ToString(true)));
        }
        return static_cast<size_t>(xla::ShapeUtil::ByteSizeOf(shape));
    }

    // The options: a base that ignores XLA_FLAGS; a single thread, so that
    // ParallelTaskAssigner doesn't split kernels by the compiling host's
    // cores; every integer dot as LLVM code, rather than a call to Eigen
    // (multi_thread_eigen and the small-GEMM limit) or a YNNPACK fusion,
    // whose kernels pick an implementation by CPU at run time; and the
    // memory-minimizing schedule, as nothing runs concurrently
    xla::HloModuleConfig module_config()
    {
        xla::DebugOptions debug = xla::DefaultDebugOptionsIgnoringFlags();
        debug.set_xla_cpu_multi_thread_eigen(false);
        debug.clear_xla_cpu_experimental_ynn_fusion_type();
        (*debug.mutable_xla_backend_extra_options())
            ["xla_force_enable_experimental_llvm_ir_gemm"] = "";
        debug.set_xla_cpu_enable_concurrency_optimized_scheduler(false);
        xla::HloModuleConfig config;
        config.set_debug_options(debug);
        config.set_intra_op_parallelism_threads(1);
        return config;
    }

    absl::StatusOr<std::unique_ptr<monad_xla_executable>> compile(
        absl::string_view const hlo, monad_xla_options const &options,
        char **const optimized_hlo)
    {
        xla::HloParserOptions parser_options;
        parser_options.set_fill_shortform_constants_with_random_values(false);
        auto parsed = xla::ParseAndReturnUnverifiedModule(
            hlo, module_config(), parser_options);
        if (!parsed.ok()) {
            return absl::InvalidArgumentError(parsed.status().message());
        }
        std::unique_ptr<xla::HloModule> module = *std::move(parsed);

        xla::Compiler::CompileOptions compile_options;
        compile_options.cpu_target_config.emplace(
            xla::cpu::TargetMachineOptions(
                "x86_64-unknown-linux-gnu",
                options.cpu ? options.cpu : "",
                options.features ? options.features : ""));
        xla::cpu::CpuCompiler compiler;
        auto optimized = compiler.RunHloPasses(
            std::move(module), /*stream_exec=*/nullptr, compile_options);
        if (!optimized.ok()) {
            return optimized.status();
        }
        module = *std::move(optimized);
        if (optimized_hlo) {
            *optimized_hlo = copy_string(module->ToString());
        }
        xla::ProgramShape const program_shape =
            module->entry_computation_layout().ComputeProgramShape();
        auto executable = compiler.RunBackend(
            std::move(module), /*stream_exec=*/nullptr, compile_options);
        if (!executable.ok()) {
            return executable.status();
        }
        auto nanort = xla::cpu::NanoRtExecutable::Create(
            *std::move(executable), program_shape);
        if (!nanort.ok()) {
            return nanort.status();
        }

        auto result = std::make_unique<monad_xla_executable>();
        result->nanort = *std::move(nanort);
        for (xla::Shape const &parameter : program_shape.parameters()) {
            auto const size = array_size(parameter);
            if (!size.ok()) {
                return size.status();
            }
            result->parameter_sizes.push_back(*size);
        }
        xla::Shape const &root = program_shape.result();
        if (!root.IsTuple()) {
            return absl::InvalidArgumentError("the root isn't a tuple");
        }
        for (xla::Shape const &element : root.tuple_shapes()) {
            auto const size = array_size(element);
            if (!size.ok()) {
                return size.status();
            }
            result->result_sizes.push_back(*size);
        }
        result->temp_size = result->nanort->temp_buffer_size();
        return result;
    }
}

extern "C"
{
monad_xla_status monad_xla_compile(
    char const *const hlo, size_t const hlo_size,
    monad_xla_options const *const options, monad_xla_executable **out,
    char **optimized_hlo, char **error)
{
    *out = nullptr;
    if (optimized_hlo) {
        *optimized_hlo = nullptr;
    }
    if (error) {
        *error = nullptr;
    }
    auto compiled = compile(
        absl::string_view(hlo, hlo_size),
        options ? *options : monad_xla_options{nullptr, nullptr},
        optimized_hlo);
    if (!compiled.ok()) {
        return fail(
            absl::IsInvalidArgument(compiled.status())
                ? MONAD_XLA_INVALID_ARGUMENT
                : MONAD_XLA_INTERNAL,
            compiled.status(),
            error);
    }
    *out = compiled->release();
    return MONAD_XLA_OK;
}

size_t monad_xla_parameter_count(monad_xla_executable const *const e)
{
    return e->parameter_sizes.size();
}

size_t monad_xla_parameter_size(monad_xla_executable const *const e, size_t i)
{
    return e->parameter_sizes[i];
}

size_t monad_xla_result_count(monad_xla_executable const *const e)
{
    return e->result_sizes.size();
}

size_t monad_xla_result_size(monad_xla_executable const *const e, size_t i)
{
    return e->result_sizes[i];
}

size_t monad_xla_temp_size(monad_xla_executable const *const e)
{
    return e->temp_size;
}

monad_xla_status monad_xla_run(
    monad_xla_executable const *const e, void const *const *parameters,
    void *const *results, void *const temp)
{
    using Executable = xla::cpu::NanoRtExecutable;
    absl::InlinedVector<Executable::Argument, 16> arguments;
    for (size_t i = 0; i < e->parameter_sizes.size(); i++) {
        arguments.emplace_back(
            parameters[i], static_cast<int64_t>(e->parameter_sizes[i]));
    }
    absl::InlinedVector<Executable::Result, 16> outputs;
    for (size_t i = 0; i < e->result_sizes.size(); i++) {
        outputs.emplace_back(
            results[i], static_cast<int64_t>(e->result_sizes[i]));
    }
    Executable::PreallocatedTemp const scratch(
        static_cast<std::byte *>(temp), e->temp_size);
    auto const event = e->nanort->Execute(arguments, outputs, scratch);
    // Without a thread pool, every thunk runs to completion on this thread
    // before Execute returns
    if (!event.IsAvailable() || event.IsError()) {
        return MONAD_XLA_INTERNAL;
    }
    return MONAD_XLA_OK;
}

void monad_xla_destroy(monad_xla_executable *const e)
{
    delete e;
}

void monad_xla_free(void *const p)
{
    std::free(p);
}
}
