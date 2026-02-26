package(default_visibility = ["//visibility:public"])

# evmc — header-only EVM-C interface
cc_library(
    name = "evmc",
    hdrs = glob(["evmc/include/evmc/**/*.h", "evmc/include/evmc/**/*.hpp"]),
    includes = ["evmc/include"],
)

# evmc::mocked_host — header-only mock host for testing
cc_library(
    name = "evmc_mocked_host",
    hdrs = ["evmc/include/evmc/mocked_host.hpp"],
    includes = ["evmc/include"],
    deps = [":evmc"],
)

# intx — header-only extended integer library
cc_library(
    name = "intx",
    hdrs = glob(["intx/include/intx/**/*.hpp"]),
    includes = ["intx/include"],
)

# ethash::keccak — single C file keccak implementation
cc_library(
    name = "ethash_keccak",
    srcs = [
        "ethash/lib/keccak/keccak.c",
        "ethash/lib/support/attributes.h",
    ],
    hdrs = glob(["ethash/include/ethash/*.h", "ethash/include/ethash/*.hpp"]),
    includes = ["ethash/include", "ethash/lib"],
)

# asmjit — JIT assembler library (static build)
cc_library(
    name = "asmjit",
    srcs = glob(["asmjit/src/asmjit/**/*.cpp"]),
    hdrs = glob(["asmjit/src/asmjit/**/*.h"]),
    includes = ["asmjit/src"],
    defines = ["ASMJIT_STATIC"],
    copts = ["-std=c++17"],
)

# quill — logging library with bundled fmt
cc_library(
    name = "quill",
    srcs = glob(["quill/quill/src/**/*.cpp", "quill/quill/src/**/*.cc"]),
    hdrs = glob([
        "quill/quill/include/**/*.h",
    ]),
    includes = ["quill/quill/include"],
    copts = ["-std=c++17"],
    defines = ["QUILL_ROOT_LOGGER_ONLY"],
)

# ankerl — header-only robin_hood hash map
cc_library(
    name = "ankerl_hash",
    hdrs = ["ankerl/robin_hood.h"],
    includes = ["ankerl"],
)

# komihash — header-only hash function
cc_library(
    name = "komihash",
    hdrs = ["komihash/komihash.h"],
    includes = ["komihash"],
)

# unordered_dense — header-only hash map
cc_library(
    name = "unordered_dense",
    hdrs = ["unordered_dense/include/ankerl/unordered_dense.h"],
    includes = ["unordered_dense/include"],
)

# blake3 — BLAKE3 hash with x86_64 assembly dispatch
cc_library(
    name = "blake3",
    srcs = [
        "BLAKE3/c/blake3.c",
        "BLAKE3/c/blake3_dispatch.c",
        "BLAKE3/c/blake3_portable.c",
        "BLAKE3/c/blake3_impl.h",
        "BLAKE3/c/blake3_avx2_x86-64_unix.S",
        "BLAKE3/c/blake3_avx512_x86-64_unix.S",
        "BLAKE3/c/blake3_sse2_x86-64_unix.S",
        "BLAKE3/c/blake3_sse41_x86-64_unix.S",
    ],
    hdrs = ["BLAKE3/c/blake3.h"],
    includes = ["BLAKE3/c"],
    copts = ["-std=c99"],
)

# openssl keccak asm — used by category/core/keccak_impl.S
cc_library(
    name = "openssl_keccak_asm",
    hdrs = glob(["openssl/crypto/sha/asm/*.S"]),
    includes = ["openssl"],
)

# cthash — header-only compile-time hashing (SHA3/keccak)
cc_library(
    name = "cthash",
    hdrs = glob(["cthash/include/**/*.hpp"]),
    includes = ["cthash/include"],
)

# concurrentqueue — header-only lock-free concurrent queue
cc_library(
    name = "concurrentqueue_lib",
    hdrs = glob(["concurrentqueue/*.h"], exclude = ["concurrentqueue/tests/**", "concurrentqueue/benchmarks/**"]),
    includes = ["concurrentqueue"],
)

# blst — BLS12-381 cryptographic library
cc_library(
    name = "blst",
    srcs = [
        "blst/src/server.c",
        "blst/build/assembly.S",
    ],
    hdrs = [
        "blst/bindings/blst.h",
        "blst/bindings/blst_aux.h",
        "blst/bindings/blst.hpp",
    ],
    textual_hdrs = glob([
        "blst/src/*.h",
        "blst/src/*.c",
        "blst/build/elf/*.s",
    ], exclude = ["blst/src/server.c"]),
    includes = ["blst/bindings"],
    copts = [
        "-fno-builtin",
        "-D__ADX__",
        "-mno-avx",
    ],
)

# secp256k1 — elliptic curve cryptography (inside silkpre)
cc_library(
    name = "secp256k1",
    srcs = ["silkpre/third_party/secp256k1/src/secp256k1.c"],
    hdrs = glob(["silkpre/third_party/secp256k1/include/**/*.h"]),
    textual_hdrs = glob([
        "silkpre/third_party/secp256k1/src/**/*.h",
    ]),
    includes = ["silkpre/third_party/secp256k1/include"],
    defines = [
        "USE_NUM_NONE",
        "USE_FIELD_INV_BUILTIN",
        "USE_SCALAR_INV_BUILTIN",
        "USE_FIELD_5X52",
        "USE_SCALAR_4X64",
        "HAVE___INT128",
        "ECMULT_WINDOW_SIZE=15",
        "ECMULT_GEN_PREC_BITS=4",
        "USE_ENDOMORPHISM",
        "ENABLE_MODULE_ECDH",
        "ENABLE_MODULE_RECOVERY",
    ],
    copts = [
        "-Wno-unused-function",
        "-Wno-sign-conversion",
        "-Wno-conversion",
    ],
)

# libff — finite field arithmetic for alt_bn128 pairing
cc_library(
    name = "libff",
    srcs = glob([
        "silkpre/third_party/libff/libff/algebra/curves/alt_bn128/*.cpp",
        "silkpre/third_party/libff/libff/common/*.cpp",
    ]),
    hdrs = glob([
        "silkpre/third_party/libff/libff/**/*.hpp",
        "silkpre/third_party/libff/libff/**/*.tcc",
    ]),
    includes = ["silkpre/third_party/libff"],
    defines = [
        "CURVE_ALT_BN128",
        "BINARY_OUTPUT",
        "MONTGOMERY_OUTPUT",
        "NO_PROCPS",
    ],
    copts = [
        "-std=c++17",
        "-fno-exceptions",
        "-Wno-unused-parameter",
        "-Wno-conversion",
        "-Wno-sign-conversion",
    ],
    deps = ["@gmp.dev//:gmp"],
)

# silkpre — Ethereum precompiled contracts
cc_library(
    name = "silkpre",
    srcs = [
        "silkpre/lib/silkpre/blake2b.c",
        "silkpre/lib/silkpre/ecdsa.c",
        "silkpre/lib/silkpre/precompile.cpp",
        "silkpre/lib/silkpre/rmd160.c",
        "silkpre/lib/silkpre/secp256k1n.cpp",
        "silkpre/lib/silkpre/sha256.c",
    ],
    hdrs = [
        "silkpre/lib/silkpre/blake2b.h",
        "silkpre/lib/silkpre/ecdsa.h",
        "silkpre/lib/silkpre/precompile.h",
        "silkpre/lib/silkpre/rmd160.h",
        "silkpre/lib/silkpre/secp256k1n.hpp",
        "silkpre/lib/silkpre/sha256.h",
    ],
    includes = ["silkpre/lib"],
    copts = [
        "-Wno-conversion",
        "-Wno-sign-conversion",
    ],
    cxxopts = ["-std=c++20"],
    deps = [
        ":ethash_keccak",
        ":intx",
        ":libff",
        ":secp256k1",
        "@gmp.dev//:gmp",
    ],
)


# c-kzg-4844 — KZG commitments for EIP-4844 (blob transactions)
# Generate trusted_setup.cpp with binary data from trusted_setup.txt
genrule(
    name = "c_kzg_trusted_setup_cpp",
    srcs = ["c-kzg-4844/src/trusted_setup.txt"],
    outs = ["c_kzg_trusted_setup.cpp"],
    cmd = """
cat > $@ << 'HEADER'
#include <c-kzg-4844/trusted_setup.hpp>
#include <cstdint>
#include <span>
namespace c_kzg_4844 {
namespace {
inline constexpr uint8_t embedded_data[] = {
HEADER
od -An -tx1 -v $(location c-kzg-4844/src/trusted_setup.txt) | sed 's/[0-9a-f][0-9a-f]/0x&,/g' >> $@
cat >> $@ << 'FOOTER'
};
}
std::span<uint8_t const> trusted_setup_data() noexcept {
    static_assert(sizeof(embedded_data) == 807177);
    return {&embedded_data[0], sizeof(embedded_data)};
}
}
FOOTER
""",
)

cc_library(
    name = "c_kzg_4844",
    srcs = [
        "c-kzg-4844/src/ckzg.c",
        ":c_kzg_trusted_setup_cpp",
    ],
    hdrs = [
        "c-kzg-4844/src/ckzg.h",
        "c-kzg-4844-builder/src/c-kzg-4844/trusted_setup.hpp",
    ],
    textual_hdrs = glob([
        "c-kzg-4844/src/**/*.h",
        "c-kzg-4844/src/**/*.c",
    ], exclude = ["c-kzg-4844/src/ckzg.c", "c-kzg-4844/src/ckzg.h"]),
    includes = [
        "c-kzg-4844/src",
        "c-kzg-4844-builder/src",
    ],
    copts = [
        "-Wno-missing-braces",
        "-Wno-unused-parameter",
        "-Wno-format",
        "-Wno-c23-extensions",
        "-Wno-conversion",
        "-Wno-sign-conversion",
    ],
    cxxopts = ["-std=c++23"],
    deps = [":blst"],
)
