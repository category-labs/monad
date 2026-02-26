load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "vm",
    srcs = [
        "compiler.cpp",
        "memory_pool.cpp",
        "varcode_cache.cpp",
        "vm.cpp",
    ],
    hdrs = [
        "code.hpp",
        "compiler.hpp",
        "host.hpp",
        "memory_pool.hpp",
        "varcode_cache.hpp",
        "vm.hpp",
    ],
    deps = [
        "@onetbb.dev//:onetbb",
        "//third_party:asmjit",
        "//third_party:evmc",
        "//third_party:intx",
        "//third_party:quill",
        "//category/vm/compiler",
        "//category/vm/core",
        "//category/vm/interpreter",
        "//category/vm/runtime",
        "//category/vm/utils",
    ],
    visibility = ["//visibility:public"],
)
