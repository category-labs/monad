load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "async",
    srcs = [
        "io.cpp",
        "storage_pool.cpp",
        "util.cpp",
    ],
    hdrs = glob([
        "*.hpp",
        "detail/*.hpp",
    ]),
    deps = [
        "//category/core",
        "//third_party:quill",
        "//third_party:unordered_dense",
        "@boost.dev//:boost",
        "@liburing.dev//:liburing",
    ],
    visibility = ["//visibility:public"],
)
