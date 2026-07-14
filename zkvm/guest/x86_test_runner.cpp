// Copyright (C) 2025-26 Category Labs, Inc.
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

// x86 host driver — parallel role to the Rust scaffolds in zkvm/zisk/ and
// zkvm/sp1/program/. Implements read_input / write_output (eth-act ABI from
// third_party/zkevm-standards io-interface/zkvm_io.h) against a --input
// <path> CLI; output goes to stdout or --output <path>. The driver compiles
// directly into the executable alongside zkvm/guest/ffi.cpp; no intermediate
// static library.

#include <io-interface/zkvm_io.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <ios>
#include <iterator>
#include <string>
#include <string_view>
#include <vector>

// The guest entry to drive. Defaults to the witness executor; the precompile
// test runner compiles this file with -DMONAD_ZKVM_X86_ENTRY set to the
// precompile-vector entry instead.
#ifndef MONAD_ZKVM_X86_ENTRY
    #define MONAD_ZKVM_X86_ENTRY monad_zkvm_execute_witness
#endif
extern "C" void MONAD_ZKVM_X86_ENTRY(void);

namespace
{
    std::vector<std::uint8_t> g_input;
    // stdout, or the --output file. Opened once in main — the guest may emit
    // its output in several write_output calls (e.g. the precompile
    // harness), and reopening would truncate the earlier chunks.
    std::FILE *g_out = nullptr;
    bool g_output_failed = false;

    void usage(char const *const prog)
    {
        std::fprintf(
            stderr, "Usage: %s --input <path> [--output <path>]\n", prog);
    }
}

extern "C" void
read_input(std::uint8_t const **const buf_ptr, std::size_t *const buf_size)
{
    *buf_ptr = g_input.data();
    *buf_size = g_input.size();
}

extern "C" void
write_output(std::uint8_t const *const output, std::size_t const size)
{
    if (std::fwrite(output, 1, size, g_out) != size) {
        g_output_failed = true;
    }
}

int main(int const argc, char **const argv)
{
    std::string input_path;
    std::string output_path;
    for (int i = 1; i < argc; ++i) {
        std::string_view const arg{argv[i]};
        if ((arg == "--input" || arg == "-i") && i + 1 < argc) {
            input_path = argv[++i];
        }
        else if ((arg == "--output" || arg == "-o") && i + 1 < argc) {
            output_path = argv[++i];
        }
        else {
            usage(argv[0]);
            return 1;
        }
    }
    if (input_path.empty()) {
        usage(argv[0]);
        return 1;
    }

    std::ifstream in{input_path, std::ios::binary};
    if (!in) {
        std::fprintf(stderr, "failed to open %s\n", input_path.c_str());
        return 1;
    }
    g_input.assign(
        std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{});

    if (output_path.empty()) {
        g_out = stdout;
    }
    else {
        g_out = std::fopen(output_path.c_str(), "wb");
        if (g_out == nullptr) {
            std::fprintf(stderr, "failed to open %s\n", output_path.c_str());
            return 1;
        }
    }

    MONAD_ZKVM_X86_ENTRY();

    // A short write, a failed flush, or a failed close all mean the output is
    // missing or truncated; report that rather than a successful run.
    if (std::fflush(g_out) != 0 || std::ferror(g_out) != 0) {
        g_output_failed = true;
    }
    if (g_out != stdout && std::fclose(g_out) != 0) {
        g_output_failed = true;
    }
    if (g_output_failed) {
        std::fprintf(stderr, "failed to write output\n");
        return 1;
    }
    return 0;
}
