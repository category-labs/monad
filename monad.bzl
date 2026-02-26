"""Shared compile options and toolchain configuration for the monad project."""

load("@rules_nixpkgs_cc//:cc.bzl", "nixpkgs_cc_configure")

# Compile options

MONAD_COPTS = [
    "-march=haswell",
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
]

def _monad_copts(copts):
    return MONAD_COPTS + select({
        "//:compiler_gcc": MONAD_COPTS_GCC,
        "//:compiler_clang": MONAD_COPTS_CLANG,
    }) + copts

MONAD_CONLYOPTS = ["-std=c23"]
MONAD_CXXOPTS = ["-std=c++23"]

def monad_cc_library(name, srcs = [], hdrs = [], deps = [], copts = [], defines = [], includes = [], **kwargs):
    """cc_library with monad standard compile options."""
    native.cc_library(
        name = name,
        srcs = srcs,
        hdrs = hdrs,
        deps = deps,
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
        nix_file_content = "(import <nixpkgs> {}).llvmPackages_19_libstdcxx_gcc_15_slim.stdenv.cc",
        register = False,
    )

cc_configure = module_extension(
    implementation = _cc_configure_impl,
)