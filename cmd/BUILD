load("//:monad.bzl", "monad_cc_binary")

# Generate git commit hash header at build time
genrule(
    name = "git_commit_hash",
    outs = ["git_commit_hash.h"],
    cmd = """
hash=$$(git rev-parse HEAD 2>/dev/null || echo unknown)
if ! git diff --quiet 2>/dev/null; then
    hash="$${hash}-dirty"
fi
echo '#define GIT_COMMIT_HASH "'"$$hash"'"' > $@
""",
    local = True,
)

# monad — main node binary
monad_cc_binary(
    name = "monad",
    srcs = [
        "monad/main.cpp",
        "monad/event.cpp",
        "monad/event.hpp",
        "monad/file_io.cpp",
        "monad/file_io.hpp",
        "monad/runloop_ethereum.cpp",
        "monad/runloop_ethereum.hpp",
        "monad/runloop_monad.cpp",
        "monad/runloop_monad.hpp",
        "monad/runloop_monad_ethblocks.cpp",
        "monad/runloop_monad_ethblocks.hpp",
        ":git_commit_hash",
    ],
    copts = ["-include", "$(location :git_commit_hash)"],
    deps = [
        "//category/core",
        "//category/execution",
        "//category/mpt",
        "//category/statesync",
        "//category/vm:vm",
        "//category/vm/evm",
        "//third_party:blake3",
        "//third_party:quill",
        "@boost.dev//:boost",
        "@cli11//:cli11",
    ],
    visibility = ["//visibility:public"],
)

# monad-cli — CLI inspection tool
monad_cc_binary(
    name = "monad-cli",
    srcs = [
        "monad_cli.cpp",
        ":git_commit_hash",
    ],
    copts = ["-include", "$(location :git_commit_hash)"],
    deps = [
        "//category/core",
        "//category/execution",
        "//category/mpt",
        "//third_party:quill",
        "@cli11//:cli11",
    ],
    visibility = ["//visibility:public"],
)
