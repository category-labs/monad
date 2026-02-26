load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "utils",
    hdrs = [
        "evm-as_utils.hpp",
        "test_context.hpp",
        "test_memory.hpp",
        "test_message.hpp",
    ],
    deps = [
        "//category/core",
        "//category/vm/compiler",
        "//category/vm/core",
        "//category/vm/interpreter",
        "//category/vm/runtime",
        "//category/vm/utils",
        "//third_party:evmc",
    ],
    visibility = ["//visibility:public"],
)
