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

// Writes a corpus of execution witnesses to a directory, plus a manifest of
// the roots each one should make the guest publish.

#include <zkvm/test/corpus/corpus_builder.hpp>
#include <zkvm/test/corpus/scenarios.hpp>

#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>

#include <cstdio>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <string>
#include <string_view>

namespace
{
    int usage(char const *const prog)
    {
        std::fprintf(
            stderr,
            "Usage: %s --out <dir> [--scenario all|transfers|evm|spoke]\n"
            "          [--seed <64 hex>]\n",
            prog);
        return 1;
    }

    std::string hex_of(monad::bytes32_t const &b)
    {
        static char const *const D = "0123456789abcdef";
        std::string s = "0x";
        for (unsigned char const c : b.bytes) {
            s.push_back(D[c >> 4]);
            s.push_back(D[c & 0xf]);
        }
        return s;
    }
}

int main(int const argc, char **const argv)
{
    std::string out_dir;
    std::string want = "all";
    monad::bytes32_t seed{};
    seed.bytes[31] = 1;

    for (int i = 1; i < argc; ++i) {
        std::string_view const arg{argv[i]};
        if (arg == "--out" && i + 1 < argc) {
            out_dir = argv[++i];
        }
        else if (arg == "--scenario" && i + 1 < argc) {
            want = argv[++i];
        }
        else if (arg == "--seed" && i + 1 < argc) {
            std::string_view h{argv[++i]};
            if (h.starts_with("0x")) {
                h.remove_prefix(2);
            }
            if (h.size() != 64) {
                std::fprintf(stderr, "corpus-gen: --seed needs 64 hex\n");
                return 1;
            }
            for (unsigned j = 0; j < 32; ++j) {
                auto const hi = monad::from_hex_char(h[2 * j]);
                auto const lo = monad::from_hex_char(h[2 * j + 1]);
                if (!hi.has_value() || !lo.has_value()) {
                    std::fprintf(stderr, "corpus-gen: --seed is not hex\n");
                    return 1;
                }
                seed.bytes[j] =
                    static_cast<unsigned char>((hi.value() << 4) | lo.value());
            }
        }
        else {
            return usage(argv[0]);
        }
    }
    if (out_dir.empty()) {
        return usage(argv[0]);
    }

    std::filesystem::create_directories(out_dir);
    std::ofstream manifest{out_dir + "/manifest.csv"};
    manifest << "scenario,number,pre_root,post_root,block_hash,txs,gas_used,"
                "witness_bytes\n";

    unsigned written = 0;
    for (auto const &s : monad::corpus::all_scenarios(seed)) {
        if (want != "all" && want != s.name) {
            continue;
        }
        monad::corpus::CorpusBuilder builder{s.genesis};
        for (auto &spec : s.blocks(builder)) {
            auto const n_txs = spec.txs.size();
            auto const e = builder.add_block(std::move(spec));

            char name[128];
            std::snprintf(
                name,
                sizeof(name),
                "%s/%s-%08lu.witness",
                out_dir.c_str(),
                s.name.c_str(),
                static_cast<unsigned long>(e.header.number));
            std::ofstream f{name, std::ios::binary};
            f.write(
                reinterpret_cast<char const *>(e.witness.data()),
                static_cast<std::streamsize>(e.witness.size()));
            if (!f) {
                std::fprintf(stderr, "corpus-gen: cannot write %s\n", name);
                return 1;
            }

            manifest << s.name << ',' << e.header.number << ','
                     << hex_of(e.pre_root) << ',' << hex_of(e.post_root) << ','
                     << hex_of(e.block_hash) << ',' << n_txs << ','
                     << e.header.gas_used << ',' << e.witness.size() << '\n';
            ++written;
        }
    }

    if (written == 0) {
        std::fprintf(
            stderr, "corpus-gen: no scenario named '%s'\n", want.c_str());
        return 1;
    }
    std::fprintf(
        stderr,
        "corpus-gen: wrote %u witnesses to %s\n",
        written,
        out_dir.c_str());
    return 0;
}
