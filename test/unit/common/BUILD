load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "common",
    hdrs = [
        "include/monad/test/config.hpp",
        "include/monad/test/environment.hpp",
        "include/monad/test/traits_test.hpp",
    ],
    includes = ["include"],
    deps = [
        "//category/core",
        "//category/execution",
        "//category/vm/evm",
        "//third_party:evmc",
        "//third_party:quill",
        "@gtest.dev//:gtest",
    ],
    visibility = ["//visibility:public"],
)
