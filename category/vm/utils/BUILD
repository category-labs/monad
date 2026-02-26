load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "utils",
    srcs = select({
        "//:zkvm": [],
        "//conditions:default": [
            "debug.cpp",
            "evm-as/compiler.cpp",
            "evmc_utils.cpp",
            "parser.cpp",
        ],
    }),
    hdrs = [
        "debug.hpp",
        "evmc_utils.hpp",
        "load_program.hpp",
        "log_utils.hpp",
        "lru_weight_cache.hpp",
        "parser.hpp",
        "rc_ptr.hpp",
        "scope_exit.hpp",
        "traits.hpp",
    ] + select({
        "//:zkvm": [],
        "//conditions:default": [
            "evm-as.hpp",
            "evm-as/builder.hpp",
            "evm-as/compiler.hpp",
            "evm-as/instruction.hpp",
            "evm-as/kernel-builder.hpp",
            "evm-as/resolver.hpp",
            "evm-as/sugar.hpp",
            "evm-as/utils.hpp",
            "evm-as/validator.hpp",
        ],
    }),
    deps = [
        "//category/vm/core",
        "//category/vm/evm",
        "//category/vm/runtime",
    ],
    visibility = ["//visibility:public"],
)
