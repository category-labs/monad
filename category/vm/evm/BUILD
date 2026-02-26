load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "evm",
    srcs = ["delegation.cpp"],
    hdrs = [
        "delegation.hpp",
        "explicit_traits.hpp",
        "monad/revision.h",
        "opcodes.hpp",
        "opcodes_xmacro.hpp",
        "switch_traits.hpp",
        "traits.hpp",
    ],
    deps = [
        "//third_party:evmc",
        "//category/vm/core",
    ],
    visibility = ["//visibility:public"],
)
