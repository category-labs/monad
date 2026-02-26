load("//:monad.bzl", "monad_cc_library")

# Shadow headers (uint256.hpp, allocator.hpp, exit.hpp).
# Dependency tracking only — the actual include path is set via
# -Icategory/zkvm/include in MONAD_COPTS for zkVM builds.
cc_library(
    name = "zkvm_hdrs",
    hdrs = glob(["include/**/*.hpp"]),
    visibility = ["//visibility:public"],
)

# Bare-metal libc/libstdcxx stubs
monad_cc_library(
    name = "zkvm_stubs",
    srcs = [
        "src/libc.cpp",
        "src/libstdcxx.cpp",
    ],
    deps = [],
    target_compatible_with = ["@platforms//cpu:riscv64"],
)

# Single monolithic static library (equivalent to CMake's libmonad-zkvm.a).
# Uses native Bazel 8 cc_static_library to merge all transitive .o files.
cc_static_library(
    name = "libmonad-zkvm",
    deps = [
        ":zkvm_stubs",
        "//category/vm/core",
        "//category/vm/evm",
        "//category/vm/interpreter",
        "//category/vm/runtime",
    ],
    features = ["-symbol_check"],
    target_compatible_with = ["@platforms//cpu:riscv64"],
    visibility = ["//visibility:public"],
)
