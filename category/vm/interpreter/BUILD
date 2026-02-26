load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "interpreter",
    srcs = [
        "execute.cpp",
        "instruction_stats.cpp",
        "intercode.cpp",
    ] + select({
        "//:zkvm": [],
        "//conditions:default": ["entry.S"],
    }),
    hdrs = [
        "call_runtime.hpp",
        "debug.hpp",
        "execute.hpp",
        "instruction_stats.hpp",
        "instruction_table.hpp",
        "instructions_fwd.hpp",
        "intercode.hpp",
        "push.hpp",
        "stack.hpp",
        "types.hpp",
    ],
    deps = [
        "//third_party:evmc",
        "//third_party:intx",
        "//category/vm/core",
        "//category/vm/evm",
        "//category/vm/runtime",
        "//category/vm/utils",
    ],
    visibility = ["//visibility:public"],
)
