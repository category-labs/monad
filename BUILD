# Root BUILD file — required for .bzl files to be loadable.

load("@bazel_skylib//lib:selects.bzl", "selects")

config_setting(
    name = "compiler_gcc",
    define_values = {"compiler": "gcc"},
)

config_setting(
    name = "compiler_clang",
    define_values = {"compiler": "clang"},
)

config_setting(
    name = "zkvm_zisk",
    define_values = {"zkvm_backend": "zisk"},
)

config_setting(
    name = "zkvm_sp1",
    define_values = {"zkvm_backend": "sp1"},
)

selects.config_setting_group(
    name = "zkvm",
    match_any = [":zkvm_zisk", ":zkvm_sp1"],
)

platform(
    name = "riscv64_none",
    constraint_values = [
        "@platforms//cpu:riscv64",
        "@platforms//os:none",
    ],
)
