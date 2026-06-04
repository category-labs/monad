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
// zkvm/core/zkvm_io.h) against a --input <path> CLI; output goes to stdout
// or --output <path>. The driver compiles directly into the executable
// alongside zkvm/guest/ffi.cpp; no intermediate static library.

#include <zkvm/core/zkvm_io.h>

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

extern "C" void monad_zkvm_execute_witness(void);

namespace
{
    std::vector<std::uint8_t> g_input;
    std::string g_output_path;

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
    if (g_output_path.empty()) {
        std::fwrite(output, 1, size, stdout);
    }
    else {
        std::ofstream out{g_output_path, std::ios::binary};
        out.write(
            reinterpret_cast<char const *>(output),
            static_cast<std::streamsize>(size));
    }
}

int main(int const argc, char **const argv)
{
    std::string input_path;
    for (int i = 1; i < argc; ++i) {
        std::string_view const arg{argv[i]};
        if ((arg == "--input" || arg == "-i") && i + 1 < argc) {
            input_path = argv[++i];
        }
        else if ((arg == "--output" || arg == "-o") && i + 1 < argc) {
            g_output_path = argv[++i];
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

    monad_zkvm_execute_witness();
    return 0;
}
