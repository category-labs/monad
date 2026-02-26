load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "runtime",
    srcs = [
        "allocator.cpp",
        "context.cpp",
        "exit.cpp",
        "storage.cpp",
    ] + select({
        "//:zkvm": [],
        "//conditions:default": [
            "context.S",
            "exit.S",
            "math.S",
            "transmute.S",
        ],
    }),
    hdrs = [
        "allocator.hpp",
        "bin.hpp",
        "cached_allocator.hpp",
        "call.hpp",
        "create.hpp",
        "data.hpp",
        "detail.hpp",
        "environment.hpp",
        "keccak.hpp",
        "log.hpp",
        "math.hpp",
        "memory.hpp",
        "runtime.hpp",
        "selfdestruct.hpp",
        "storage.hpp",
        "storage_costs.hpp",
        "transmute.hpp",
        "types.hpp",
    ],
    deps = [
        "//third_party:evmc",
        "//third_party:ethash_keccak",
        "//third_party:intx",
        "//category/vm/core",
        "//category/vm/evm",
    ] + select({
        "//:zkvm": ["//category/core:core_hdrs"],
        "//conditions:default": ["//category/core"],
    }),
    visibility = ["//visibility:public"],
)
