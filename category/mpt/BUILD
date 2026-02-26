load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "mpt",
    srcs = [
        "compute.cpp",
        "copy_trie.cpp",
        "db.cpp",
        "find.cpp",
        "find_notify_fiber.cpp",
        "node.cpp",
        "read_node_blocking.cpp",
        "trie.cpp",
        "update_aux.cpp",
    ],
    hdrs = glob([
        "*.hpp",
        "detail/*.hpp",
        "merkle/*.hpp",
    ]),
    deps = [
        "//category/async",
        "//category/core",
        "//third_party:concurrentqueue_lib",
        "//third_party:quill",
        "@boost.dev//:boost",
        "@zstd.dev//:zstd",
    ],
    visibility = ["//visibility:public"],
)
