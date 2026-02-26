"""Shared compile options and toolchain configuration for the monad project."""

load("@rules_nixpkgs_cc//:cc.bzl", "nixpkgs_cc_configure")

# Compile options

MONAD_COPTS = select({
    "//:zkvm": ["-Icategory/zkvm/include", "-Wno-template-body"],
    "//conditions:default": ["-march=haswell"],
}) + [
    "-Wall",
    "-Wextra",
    "-Wconversion",
    "-Werror",
    "-I.",
]

MONAD_COPTS_GCC = [
    "-Wno-missing-field-initializers",
    "-Wno-attributes=clang::no_sanitize",
    "-Wno-maybe-musttail-local-addr",
]

MONAD_COPTS_CLANG = []

MONAD_DEFINES = [
    "_GNU_SOURCE",
    "QUILL_ROOT_LOGGER_ONLY",
    "JSON_HAS_RANGES=0",
] + select({
    "//:zkvm_zisk": ["MONAD_ZKVM", "MONAD_ZKVM_ZISK", "NDEBUG"],
    "//:zkvm_sp1": ["MONAD_ZKVM", "MONAD_ZKVM_SP1", "NDEBUG"],
    "//conditions:default": [],
})

def _monad_copts(copts):
    return MONAD_COPTS + select({
        "//:compiler_gcc": MONAD_COPTS_GCC,
        "//:compiler_clang": MONAD_COPTS_CLANG,
    }) + copts

MONAD_CONLYOPTS = ["-std=c23"]
MONAD_CXXOPTS = ["-std=c++23"]

_ZKVM_HDRS_DEP = select({
    "//:zkvm": ["//category/zkvm:zkvm_hdrs"],
    "//conditions:default": [],
})

def monad_cc_library(name, srcs = [], hdrs = [], deps = [], copts = [], defines = [], includes = [], **kwargs):
    """cc_library with monad standard compile options."""
    native.cc_library(
        name = name,
        srcs = srcs,
        hdrs = hdrs,
        deps = deps + _ZKVM_HDRS_DEP,
        copts = _monad_copts(copts),
        conlyopts = MONAD_CONLYOPTS,
        cxxopts = MONAD_CXXOPTS,
        defines = MONAD_DEFINES + defines,
        includes = includes,
        **kwargs
    )

def monad_cc_binary(name, srcs = [], deps = [], copts = [], defines = [], **kwargs):
    """cc_binary with monad standard compile options."""
    native.cc_binary(
        name = name,
        srcs = srcs,
        deps = deps,
        copts = _monad_copts(copts),
        conlyopts = MONAD_CONLYOPTS,
        cxxopts = MONAD_CXXOPTS,
        local_defines = MONAD_DEFINES + defines,
        **kwargs
    )

def monad_cc_test(name, srcs = [], deps = [], copts = [], defines = [], **kwargs):
    """cc_test with monad standard compile options."""
    native.cc_test(
        name = name,
        srcs = srcs,
        deps = deps,
        copts = _monad_copts(copts),
        conlyopts = MONAD_CONLYOPTS,
        cxxopts = MONAD_CXXOPTS,
        defines = MONAD_DEFINES + defines,
        **kwargs
    )

# Toolchain configuration

def _cc_configure_impl(module_ctx):
    nixpkgs_cc_configure(
        name = "nixpkgs_config_cc_gcc",
        repository = "@nixpkgs",
        nix_file_content = "(import <nixpkgs> {}).gcc15",
        register = False,
    )
    nixpkgs_cc_configure(
        name = "nixpkgs_config_cc_clang",
        repository = "@nixpkgs",
        nix_file_content = "let pkgs = import <nixpkgs> {}; in pkgs.llvmPackages_19.stdenv.cc.override { gccForLibs = pkgs.gcc15.cc; }",
        register = False,
    )
    nixpkgs_cc_configure(
        name = "nixpkgs_config_cc_riscv64",
        repository = "@nixpkgs",
        nix_file = "//:riscv64-embedded-custom-newlib.nix",
        nix_file_deps = ["//:nixpkgs.nix", "//:flake.lock"],
        cross_cpu = "riscv64",
        exec_constraints = ["@platforms//cpu:x86_64", "@platforms//os:linux"],
        target_constraints = ["@platforms//cpu:riscv64", "@platforms//os:none"],
        cc_lang = "c++",
        register = False,
    )

cc_configure = module_extension(
    implementation = _cc_configure_impl,
)