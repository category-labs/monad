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
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#ifdef MONAD_ZKVM_L2
    #include <zkvm/guest/l2_ecdh.hpp>
#endif

#include <cstdio>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <span>
#include <string>
#include <string_view>

namespace
{
    int usage(char const *const prog)
    {
        std::fprintf(
            stderr,
            "Usage: %s --out <dir> [--scenario all|transfers|evm|spoke]\n"
            "          [--seed <64 hex>] [--sk <64 hex>] [--salt <64 hex>]\n"
            "       %s --pubkey <64 hex secret>\n"
            "       %s --spoke-address [--seed <64 hex>]\n"
            "       %s --salt-commitment <64 hex secret>\n"
            "\n"
            "--sk is the operator secret, required in an L2 build and\n"
            "ignored otherwise. --pubkey prints the compressed public half of\n"
            "a secret as MONAD_ZKVM_L2_OPERATOR_PK_X and _ODD, which is what\n"
            "the guest has to be configured with before a corpus it produces\n"
            "can be decrypted. --spoke-address prints where the spoke\n"
            "scenario will deploy, which is what MONAD_ZKVM_L2_SPOKE has to\n"
            "be -- the address is CREATE-derived, so it follows the seed.\n"
            "--salt-commitment prints the keccak256 of a blinder secret as\n"
            "MONAD_ZKVM_L2_SALT_COMMITMENT; --salt hands the generator that\n"
            "same secret. Required in an L2 build: without it the block hash\n"
            "is unblinded and the state is testable by anyone who can guess\n"
            "it.\n",
            prog,
            prog,
            prog,
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

    std::string hex_of_address(monad::Address const &a)
    {
        static char const *const D = "0123456789abcdef";
        std::string s = "0x";
        for (unsigned char const c : a.bytes) {
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
    monad::bytes32_t sk{};
    bool have_sk = false;
    monad::bytes32_t salt{};
    bool have_salt = false;
    monad::bytes32_t commit_of{};
    bool want_commitment = false;
    monad::bytes32_t pubkey_of{};
    bool want_pubkey = false;
    bool want_spoke = false;

    auto const parse_hex32 = [](std::string_view h,
                                monad::bytes32_t &out) -> bool {
        if (h.starts_with("0x")) {
            h.remove_prefix(2);
        }
        if (h.size() != 64) {
            return false;
        }
        for (unsigned j = 0; j < 32; ++j) {
            auto const hi = monad::from_hex_char(h[2 * j]);
            auto const lo = monad::from_hex_char(h[2 * j + 1]);
            if (!hi.has_value() || !lo.has_value()) {
                return false;
            }
            out.bytes[j] =
                static_cast<unsigned char>((hi.value() << 4) | lo.value());
        }
        return true;
    };

    for (int i = 1; i < argc; ++i) {
        std::string_view const arg{argv[i]};
        if (arg == "--out" && i + 1 < argc) {
            out_dir = argv[++i];
        }
        else if (arg == "--scenario" && i + 1 < argc) {
            want = argv[++i];
        }
        else if (arg == "--seed" && i + 1 < argc) {
            if (!parse_hex32(argv[++i], seed)) {
                std::fprintf(stderr, "corpus-gen: --seed needs 64 hex\n");
                return 1;
            }
        }
        else if (arg == "--sk" && i + 1 < argc) {
            if (!parse_hex32(argv[++i], sk)) {
                std::fprintf(stderr, "corpus-gen: --sk needs 64 hex\n");
                return 1;
            }
            have_sk = true;
        }
        else if (arg == "--pubkey" && i + 1 < argc) {
            if (!parse_hex32(argv[++i], pubkey_of)) {
                std::fprintf(stderr, "corpus-gen: --pubkey needs 64 hex\n");
                return 1;
            }
            want_pubkey = true;
        }
        else if (arg == "--salt" && i + 1 < argc) {
            if (!parse_hex32(argv[++i], salt)) {
                std::fprintf(stderr, "corpus-gen: --salt needs 64 hex\n");
                return 1;
            }
            have_salt = true;
        }
        else if (arg == "--salt-commitment" && i + 1 < argc) {
            if (!parse_hex32(argv[++i], commit_of)) {
                std::fprintf(
                    stderr, "corpus-gen: --salt-commitment needs 64 hex\n");
                return 1;
            }
            want_commitment = true;
        }
        else if (arg == "--spoke-address") {
            want_spoke = true;
        }
        else {
            return usage(argv[0]);
        }
    }
    if (want_commitment) {
        std::printf(
            "MONAD_ZKVM_L2_SALT_COMMITMENT=%s\n",
            hex_of(monad::to_bytes(monad::keccak256(monad::byte_string_view{
                       commit_of.bytes, sizeof(commit_of.bytes)})))
                .c_str());
        return 0;
    }

    if (want_spoke) {
        // Ask the builder rather than recomputing the CREATE derivation here:
        // one derivation, and it is the one the corpus will actually use.
        for (auto const &s : monad::corpus::all_scenarios(seed)) {
            if (s.name != "spoke") {
                continue;
            }
            monad::corpus::CorpusBuilder b{s.genesis, sk, salt};
            std::printf(
                "MONAD_ZKVM_L2_SPOKE=%s\n",
                hex_of_address(
                    b.next_contract_address(monad::corpus::address_of(
                        monad::corpus::derive_key(seed, 200))))
                    .c_str());
            return 0;
        }
        std::fprintf(stderr, "corpus-gen: no spoke scenario\n");
        return 1;
    }

    if (want_pubkey) {
#ifdef MONAD_ZKVM_L2
        auto const k = monad::l2_scalar_from_be(
            std::span<unsigned char const, 32>{pubkey_of.bytes, 32});
        if (!monad::l2_scalar_is_valid(k)) {
            std::fprintf(stderr, "corpus-gen: not a secp256k1 scalar\n");
            return 1;
        }
        auto const pk = monad::l2_ecdh(k, monad::SECP256K1_G);
        if (!pk.has_value()) {
            std::fprintf(stderr, "corpus-gen: cannot derive the public key\n");
            return 1;
        }
        unsigned char sec1[33];
        monad::l2_point_compress(
            pk.value(), std::span<unsigned char, 33>{sec1});
        std::printf("MONAD_ZKVM_L2_OPERATOR_PK_X=0x");
        for (unsigned i = 1; i < 33; ++i) {
            std::printf("%02x", sec1[i]);
        }
        std::printf(
            "\nMONAD_ZKVM_L2_OPERATOR_PK_ODD=%d\n", sec1[0] == 0x03 ? 1 : 0);
        return 0;
#else
        std::fprintf(
            stderr,
            "corpus-gen: --pubkey needs an L2 build; this one has no curve\n");
        return 1;
#endif
    }

    if (out_dir.empty()) {
        return usage(argv[0]);
    }
#ifdef MONAD_ZKVM_L2
    if (!have_sk) {
        std::fprintf(
            stderr,
            "corpus-gen: --sk is required in an L2 build -- without it the "
            "leaves cannot be encrypted under the compiled operator key\n");
        return 1;
    }
    if (!have_salt) {
        std::fprintf(
            stderr,
            "corpus-gen: --salt is required in an L2 build -- a zero blinder "
            "publishes an unblinded block hash and nothing would say so\n");
        return 1;
    }
#else
    (void)have_sk;
    (void)have_salt;
#endif

    std::filesystem::create_directories(out_dir);
    std::ofstream manifest{out_dir + "/manifest.csv"};
    manifest << "scenario,number,pre_root,post_root,block_hash,parent_hash,"
                "txs,gas_used,witness_bytes,anchor,leaves\n";

    unsigned written = 0;
    for (auto const &s : monad::corpus::all_scenarios(seed)) {
        if (want != "all" && want != s.name) {
            continue;
        }
        monad::corpus::CorpusBuilder builder{s.genesis, sk, salt};
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
                     << hex_of(e.block_hash) << ',' << hex_of(e.parent_hash)
                     << ',' << n_txs << ',' << e.header.gas_used << ','
                     << e.witness.size() << ',' << hex_of(e.namespace_anchor)
                     << ',' << e.encrypted_leaves << '\n';
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
