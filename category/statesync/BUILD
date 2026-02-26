load("//:monad.bzl", "monad_cc_library")

monad_cc_library(
    name = "statesync",
    srcs = [
        "statesync_client.cpp",
        "statesync_client_context.cpp",
        "statesync_protocol.cpp",
        "statesync_server.cpp",
        "statesync_server_context.cpp",
        "statesync_thread.cpp",
        "statesync_version.cpp",
    ],
    hdrs = [
        "statesync_client.h",
        "statesync_client_context.hpp",
        "statesync_messages.h",
        "statesync_protocol.hpp",
        "statesync_server.h",
        "statesync_server_context.hpp",
        "statesync_server_network.hpp",
        "statesync_thread.hpp",
        "statesync_version.h",
    ],
    deps = [
        "//category/async",
        "//category/core",
        "//category/execution",
        "//category/mpt",
        "//third_party:quill",
    ],
    visibility = ["//visibility:public"],
)
