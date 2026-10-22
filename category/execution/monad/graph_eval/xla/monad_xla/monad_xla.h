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

// libmonad_xla.so: graph_eval's way into XLA. It compiles an HLO module, given
// as text, with XLA's CPU compiler, and runs it with XLA's NanoRt runtime,
// synchronously on the calling thread, on memory the caller provides. XLA is
// built by Bazel with its own toolchain, LLVM, Abseil and protobuf, so the
// library exports only this C API (see monad_xla.lds), and scripts/
// build_xla.sh builds it inside third_party/xla's Bazel workspace.
#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

// A compiled HLO module
typedef struct monad_xla_executable monad_xla_executable;

typedef enum
{
    MONAD_XLA_OK = 0,
    // The HLO doesn't parse, or isn't a module the library can run
    MONAD_XLA_INVALID_ARGUMENT = 1,
    // XLA failed otherwise
    MONAD_XLA_INTERNAL = 2,
} monad_xla_status;

typedef struct
{
    // The LLVM CPU to compile for, such as "znver4"
    char const *cpu;
    // LLVM features to enable or disable on top of the CPU's, such as
    // "+avx512f,+avx512vnni", or ""
    char const *features;
} monad_xla_options;

// Parses `hlo`, an HLO module as text, and compiles it for `options`' CPU,
// with options fixed for graph_eval: a single thread, every integer dot as
// LLVM code rather than a call to Eigen or YNNPACK, and no XLA_FLAGS. The
// module's parameters and its root's elements must be dense arrays, in the
// default (row-major) layout, and its root a tuple. If `optimized_hlo` isn't
// null, *optimized_hlo is the module as text after XLA's HLO passes, its
// fusions and all, to free with monad_xla_free. On failure, *error is a
// message to free with monad_xla_free
monad_xla_status monad_xla_compile(
    char const *hlo, size_t hlo_size, monad_xla_options const *options,
    monad_xla_executable **out, char **optimized_hlo, char **error);

// The bytes of each parameter, each element of the root tuple, and the
// scratch memory a run needs. monad_xla_run takes buffers of exactly these
// sizes
size_t monad_xla_parameter_count(monad_xla_executable const *executable);
size_t
monad_xla_parameter_size(monad_xla_executable const *executable, size_t i);
size_t monad_xla_result_count(monad_xla_executable const *executable);
size_t monad_xla_result_size(monad_xla_executable const *executable, size_t i);
size_t monad_xla_temp_size(monad_xla_executable const *executable);

// Runs the module, reading `parameters`, writing `results` and using `temp`
// for the values in between, synchronously on the calling thread. Every
// pointer must be 64-byte aligned; `temp` may be null if the temp size is 0.
// Concurrent runs of one executable need separate results and temps
monad_xla_status monad_xla_run(
    monad_xla_executable const *executable, void const *const *parameters,
    void *const *results, void *temp);

void monad_xla_destroy(monad_xla_executable *executable);

// Frees what the library allocates for the caller, such as error messages
void monad_xla_free(void *p);

#ifdef __cplusplus
}
#endif
