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
#include <zkvm/test/corpus/witness_stats.hpp>
#include <zkvm/test/corpus/workload.hpp>

#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/core/keccak.hpp>
#ifdef MONAD_ZKVM_L2
    #include <zkvm/guest/l2_ecdh.hpp>
#endif

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <ostream>
#include <span>
#include <string>
#include <string_view>
#include <vector>

namespace
{
    int usage(char const *const prog)
    {
        std::fprintf(
            stderr,
            "Usage: %s --out <dir> [--scenario all|transfers|evm|spoke]\n"
            "          [--seed <64 hex>] [--sk <64 hex>] [--salt <64 hex>]\n"
            "       %s --out <dir> --preset wholesale|payouts\n"
            "          [--accounts N] [--blocks N] [--distinct K]\n"
            "          [--shape zipf|uniform|hotset] [--zipf-s F]\n"
            "          [--chunk N] [--sweep K1,K2,...]\n"
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
            "it.\n"
            "\n"
            "--preset generates a benchmark corpus instead of the small\n"
            "scenarios: a genesis of --accounts holders, then --blocks blocks\n"
            "that each aim to touch --distinct of them. --distinct is the "
            "axis\n"
            "that matters -- measured over 504 mainnet witnesses, cost tracks\n"
            "witness bytes (R2 0.94) and 82%% of those bytes are digests of\n"
            "siblings the block did not touch, so what a block costs is how\n"
            "many DISTINCT leaves it reaches. --shape only changes which "
            "ones,\n"
            "and exists to check that it does not change the cost.\n"
            "--sweep runs the same workload once per distinct value, writing\n"
            "each into its own subdirectory.\n",
            prog,
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
    bool want_preset = false;
    monad::corpus::WorkloadSpec wl{};
    std::vector<uint64_t> sweep;

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
        else if (arg == "--preset" && i + 1 < argc) {
            wl.preset = monad::corpus::preset_from_name(argv[++i]);
            want_preset = true;
        }
        else if (arg == "--shape" && i + 1 < argc) {
            wl.shape = monad::corpus::shape_from_name(argv[++i]);
        }
        else if (arg == "--accounts" && i + 1 < argc) {
            wl.accounts = std::strtoull(argv[++i], nullptr, 10);
        }
        else if (arg == "--blocks" && i + 1 < argc) {
            wl.blocks = std::strtoull(argv[++i], nullptr, 10);
        }
        else if (arg == "--distinct" && i + 1 < argc) {
            wl.distinct = std::strtoull(argv[++i], nullptr, 10);
        }
        else if (arg == "--chunk" && i + 1 < argc) {
            wl.chunk = std::strtoull(argv[++i], nullptr, 10);
        }
        else if (arg == "--zipf-s" && i + 1 < argc) {
            wl.zipf_s = std::strtod(argv[++i], nullptr);
        }
        else if (arg == "--sweep" && i + 1 < argc) {
            std::string_view rest{argv[++i]};
            while (!rest.empty()) {
                auto const comma = rest.find(',');
                auto const tok = rest.substr(0, comma);
                sweep.push_back(
                    std::strtoull(std::string{tok}.c_str(), nullptr, 10));
                if (comma == std::string_view::npos) {
                    break;
                }
                rest.remove_prefix(comma + 1);
            }
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

    // One emitter for both paths: the manifest columns are the regressors,
    // and which ones they are is a measurement -- witness bytes track
    // measured cost with R2 0.94 over 504 mainnet blocks, digests are 82% of
    // those bytes, and code bytes add nothing once the leaf count is known.
    // code_bytes is here to keep confirming that, not because it is expected
    // to matter.
    auto const manifest_header =
        "scenario,number,pre_root,post_root,block_hash,parent_hash,"
        "txs,gas_used,witness_bytes,anchor,leaves,"
        "intended_distinct,acct_leaves,storage_leaves,branches,exts,digests,"
        "blob_bytes,code_bytes\n";

    auto const emit = [&](std::ostream &manifest,
                          std::string const &dir,
                          std::string const &tag,
                          monad::corpus::Emitted const &e,
                          size_t const n_txs,
                          uint64_t const intended) -> bool {
        char name[256];
        std::snprintf(
            name,
            sizeof(name),
            "%s/%s-%08lu.witness",
            dir.c_str(),
            tag.c_str(),
            static_cast<unsigned long>(e.header.number));
        std::ofstream f{name, std::ios::binary};
        f.write(
            reinterpret_cast<char const *>(e.witness.data()),
            static_cast<std::streamsize>(e.witness.size()));
        if (!f) {
            std::fprintf(stderr, "corpus-gen: cannot write %s\n", name);
            return false;
        }
        auto const st = monad::corpus::witness_stats(e.witness);
        manifest << tag << ',' << e.header.number << ',' << hex_of(e.pre_root)
                 << ',' << hex_of(e.post_root) << ',' << hex_of(e.block_hash)
                 << ',' << hex_of(e.parent_hash) << ',' << n_txs << ','
                 << e.header.gas_used << ',' << e.witness.size() << ','
                 << hex_of(e.namespace_anchor) << ',' << e.encrypted_leaves
                 << ',' << intended << ',' << st.acct_leaves << ','
                 << st.storage_leaves << ',' << st.branches << ',' << st.exts
                 << ',' << st.digests << ',' << st.blob_bytes << ','
                 << st.code_bytes << '\n';
        return true;
    };

    if (want_preset) {
        auto const distincts =
            sweep.empty() ? std::vector<uint64_t>{wl.distinct} : sweep;
        unsigned total = 0;
        for (uint64_t const d : distincts) {
            auto spec = wl;
            spec.distinct = d;
            spec.seed = seed;
            monad::corpus::Workload w{spec};
            auto const &r = w.spec();

            // A sweep gets one directory per point so the manifests stay
            // separable; a single run writes straight into --out.
            std::string const dir =
                sweep.empty()
                    ? out_dir
                    : out_dir + "/" + monad::corpus::name_of(r.preset) + "-" +
                          monad::corpus::name_of(r.shape) + "-d" +
                          std::to_string(r.distinct);
            std::filesystem::create_directories(dir);
            std::ofstream manifest{dir + "/manifest.csv"};
            manifest << manifest_header;

            std::fprintf(
                stderr,
                "corpus-gen: %s/%s accounts=%lu blocks=%lu distinct=%lu "
                "chunk=%zu gas_limit=%lu\n",
                monad::corpus::name_of(r.preset),
                monad::corpus::name_of(r.shape),
                static_cast<unsigned long>(r.accounts),
                static_cast<unsigned long>(r.blocks),
                static_cast<unsigned long>(r.distinct),
                r.chunk,
                static_cast<unsigned long>(r.gas_limit()));

            monad::corpus::CorpusBuilder builder{
                w.seeder(), r.chunk, r.gas_limit(), sk, salt};
            std::fprintf(
                stderr,
                "corpus-gen: genesis seeded, spoke at %s\n",
                hex_of_address(w.spoke()).c_str());

            std::string const tag =
                std::string{monad::corpus::name_of(r.preset)};
            for (uint64_t i = 0; i < w.block_count(); ++i) {
                auto spec_i = w.block(builder, i);
                auto const n_txs = spec_i.txs.size();
                auto const intended = w.last_intended_distinct();
                auto const e = builder.add_block(std::move(spec_i));
                if (!emit(manifest, dir, tag, e, n_txs, intended)) {
                    return 1;
                }
                ++total;
            }
        }
        std::fprintf(
            stderr,
            "corpus-gen: wrote %u witnesses to %s\n",
            total,
            out_dir.c_str());
        return 0;
    }

    std::filesystem::create_directories(out_dir);
    std::ofstream manifest{out_dir + "/manifest.csv"};
    manifest << manifest_header;

    unsigned written = 0;
    for (auto const &s : monad::corpus::all_scenarios(seed)) {
        if (want != "all" && want != s.name) {
            continue;
        }
        monad::corpus::CorpusBuilder builder{s.genesis, sk, salt};
        for (auto &spec : s.blocks(builder)) {
            auto const n_txs = spec.txs.size();
            auto const e = builder.add_block(std::move(spec));
            if (!emit(manifest, out_dir, s.name, e, n_txs, 0)) {
                return 1;
            }
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
