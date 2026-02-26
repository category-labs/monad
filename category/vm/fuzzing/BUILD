load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "fuzzing",
    srcs = ["generator/instruction_data.cpp"],
    hdrs = [
        "generator/choice.hpp",
        "generator/generator.hpp",
        "generator/instruction_data.hpp",
    ],
    deps = [
        "//category/vm/compiler",
        "//category/vm/core",
        "//category/vm/utils",
    ],
    visibility = ["//visibility:public"],
)
