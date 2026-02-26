load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "rpc",
    srcs = [
        "monad_executor.cpp",
        "overrides.cpp",
    ],
    hdrs = [
        "monad_executor.h",
        "overrides.h",
        "overrides.hpp",
    ],
    deps = [
        "//category/core",
        "//category/execution",
        "//category/mpt",
        "//category/vm:vm",
        "//category/vm/evm",
        "//third_party:evmc",
        "//third_party:intx",
        "//third_party:quill",
        "//third_party:unordered_dense",
        "//third_party/nlohmann_json:json",
        "@boost.dev//:boost",
    ],
    visibility = ["//visibility:public"],
)
