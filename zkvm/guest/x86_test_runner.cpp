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

#include <category/core/byte_string.hpp>
#include <category/core/keccak.hpp>
#include <category/crypto/hash256.h>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <io-interface/zkvm_io.h>

#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
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
    // stdout, or the --output file. Opened once in main — the guest may emit
    // its output in several write_output calls (e.g. the precompile
    // harness), and reopening would truncate the earlier chunks.
    std::FILE *g_out = nullptr;
    bool g_output_failed = false;
    // Everything the guest wrote, for --check.
    std::vector<std::uint8_t> g_output;

    void usage(char const *const prog)
    {
        std::fprintf(
            stderr,
            "Usage: %s --input <path> [--output <path>] [--check]\n",
            prog);
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
    g_output.insert(g_output.end(), output, output + size);
}

// --check: the guest's public value must be the hash of the witness's own
// block header, which is to say the computed post-state root must be the one
// the block commits to. A test aid for the host runner only; the guest never
// assumes the header it is given is honest.
bool output_matches_witness()
{
    auto const witness = monad::parse_execution_witness(
        monad::byte_string_view{g_input.data(), g_input.size()});
    if (!witness.has_value()) {
        std::fprintf(stderr, "--check: the witness does not parse\n");
        return false;
    }
    monad::byte_string_view block_view = witness.value().block_rlp;
    std::vector<monad::byte_string_view> raw_transactions;
    auto const block = monad::rlp::decode_block(block_view, raw_transactions);
    if (!block.has_value()) {
        std::fprintf(stderr, "--check: the block does not decode\n");
        return false;
    }
    monad_hash256 const want =
        monad::keccak256(monad::rlp::encode_block_header(block.value().header));
    if (g_output.size() == sizeof(want.bytes) &&
        std::memcmp(g_output.data(), want.bytes, sizeof(want.bytes)) == 0) {
        return true;
    }
    std::fprintf(stderr, "--check: block hash mismatch\n  want ");
    for (unsigned char const b : want.bytes) {
        std::fprintf(stderr, "%02x", b);
    }
    std::fprintf(stderr, "\n  got  ");
    for (unsigned char const b : g_output) {
        std::fprintf(stderr, "%02x", b);
    }
    std::fprintf(stderr, "\n");
    return false;
}

int main(int const argc, char **const argv)
{
    std::string input_path;
    std::string output_path;
    bool check = false;
    for (int i = 1; i < argc; ++i) {
        std::string_view const arg{argv[i]};
        if ((arg == "--input" || arg == "-i") && i + 1 < argc) {
            input_path = argv[++i];
        }
        else if ((arg == "--output" || arg == "-o") && i + 1 < argc) {
            output_path = argv[++i];
        }
        else if (arg == "--check") {
            check = true;
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

    // The host-side point-evaluation precompile needs the KZG trusted setup,
    // which cmd/monad/main.cpp loads at startup; the RISC-V guest routes the
    // precompile elsewhere, so only this x86 driver has to load it.
    if (!monad::init_trusted_setup()) {
        std::fprintf(stderr, "failed to load the KZG trusted setup\n");
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

    monad_zkvm_execute_witness();

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
    if (check && !output_matches_witness()) {
        return 1;
    }
    return 0;
}
