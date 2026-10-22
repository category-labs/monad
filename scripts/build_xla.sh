#!/bin/bash
#
# Builds libmonad_xla.so, graph_eval's way into XLA, from third_party/xla,
# outside the monad build: XLA's CPU compiler and NanoRt runtime, behind the C
# API in category/execution/monad/graph_eval/xla/monad_xla/monad_xla.h, in one
# shared library that exports nothing else. XLA builds with Bazel, its own
# hermetic clang 18 and Python, and its own LLVM, Abseil and protobuf, so the
# shim's package is built inside XLA's workspace, which --package_path adds it
# to as //monad_xla. It only needs rebuilding when the submodule or the shim
# changes, and needs network access the first time.
#
# XLA's pinned LLVM archive no longer downloads with its pinned checksum: the
# TensorFlow mirror doesn't have it, and GitHub makes archives on request, now
# with different compression than when the pin was made. So the archive GitHub
# serves now is pinned here instead, by the SHA-256 in LLVM_ARCHIVE_SHA256
# below, which scripts/verify_llvm_archive.sh showed to be the archive of
# exactly the pinned commit. The archive is downloaded once and kept in a
# Bazel distdir, and the submodule's LLVM_SHA256 is set to that SHA-256. Any
# other archive, or a submodule pinning another LLVM commit, stops the build:
# verify the new archive and update LLVM_COMMIT and LLVM_ARCHIVE_SHA256.
#
# Environment:
#   XLA_BUILD_DIR  build directory, for the library and the distdir (default:
#                  <repo>/build-xla)
#   BAZEL          Bazel, or Bazelisk, which reads .bazelversion (default:
#                  bazel, else ~/.local/bin/bazel)
#
# Extra arguments are passed to bazel build, e.g.
#   scripts/build_xla.sh --jobs=8

set -euo pipefail

# The LLVM commit XLA pins, and the SHA-256 of GitHub's archive of it, which
# scripts/verify_llvm_archive.sh verified on 2026-10-22
LLVM_COMMIT="909041e4802c4b9a2223ca04099f35bf1dbbd460"
LLVM_ARCHIVE_SHA256="00b1077e029fa57e6f2d9ac24936a49acf23ebc051b04f487131116258be6248"

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
xla_dir="${repo_root}/third_party/xla"
build_dir="$(realpath -m "${XLA_BUILD_DIR:-${repo_root}/build-xla}")"
distdir="${build_dir}/distdir"
shim_root="${repo_root}/category/execution/monad/graph_eval/xla"

bazel="${BAZEL:-$(command -v bazel || echo "${HOME}/.local/bin/bazel")}"
if [ ! -x "${bazel}" ]; then
  echo "No Bazel: install Bazelisk, e.g. as ~/.local/bin/bazel, from" \
    "https://github.com/bazelbuild/bazelisk/releases" >&2
  exit 1
fi
if [ -n "${XLA_FLAGS:-}" ]; then
  echo "XLA_FLAGS is set; unset it, as it would change how XLA compiles" >&2
  exit 1
fi

# The LLVM archive: the verified one, or the build stops
llvm_pin="${xla_dir}/third_party/llvm/workspace.bzl"
pinned_commit="$(sed -n 's/^ *LLVM_COMMIT = "\([0-9a-f]*\)".*/\1/p' "${llvm_pin}")"
if [ "${pinned_commit}" != "${LLVM_COMMIT}" ]; then
  echo "XLA pins LLVM ${pinned_commit}, but the verified archive is" \
    "${LLVM_COMMIT}'s: download" \
    "https://github.com/llvm/llvm-project/archive/${pinned_commit}.tar.gz," \
    "check it with scripts/verify_llvm_archive.sh, and update LLVM_COMMIT and" \
    "LLVM_ARCHIVE_SHA256 in $0" >&2
  exit 1
fi
archive="${distdir}/${LLVM_COMMIT}.tar.gz"
mkdir -p "${distdir}"
if [ ! -f "${archive}" ]; then
  curl -fL -o "${archive}.part" \
    "https://github.com/llvm/llvm-project/archive/${LLVM_COMMIT}.tar.gz"
  mv "${archive}.part" "${archive}"
fi
archive_sha256="$(sha256sum "${archive}" | cut -d' ' -f1)"
if [ "${archive_sha256}" != "${LLVM_ARCHIVE_SHA256}" ]; then
  echo "${archive}'s SHA-256 is ${archive_sha256}, not the verified" \
    "archive's, ${LLVM_ARCHIVE_SHA256}. If GitHub now serves a different" \
    "archive, check it with scripts/verify_llvm_archive.sh and update" \
    "LLVM_ARCHIVE_SHA256 in $0" >&2
  exit 1
fi
if ! grep -q "LLVM_SHA256 = \"${LLVM_ARCHIVE_SHA256}\"" "${llvm_pin}"; then
  sed -i "s/^\( *LLVM_SHA256 = \"\)[0-9a-f]*\"/\1${LLVM_ARCHIVE_SHA256}\"/" \
    "${llvm_pin}"
  echo "Set ${llvm_pin}'s LLVM_SHA256 to ${LLVM_ARCHIVE_SHA256}"
fi

cd "${xla_dir}"
if [ ! -f xla_configure.bazelrc ]; then
  python3 configure.py --backend=CPU
fi
"${bazel}" build \
  --spawn_strategy=sandboxed \
  --distdir="${distdir}" \
  --package_path="%workspace%:${shim_root}" \
  //monad_xla:libmonad_xla.so "$@"

library="${build_dir}/libmonad_xla.so"
install -m 755 "$("${bazel}" info bazel-bin)/monad_xla/libmonad_xla.so" \
  "${library}"
# Besides the API, the linker exports the bounds of a section of upb's (XLA's
# protobuf runtime), __start_pb_defaults and __stop_pb_defaults, as it does
# from XLA's own PJRT plugin
exported="$(nm -D --defined-only "${library}" | awk '{print $3}' |
  grep -v '^monad_xla_' | grep -v '^MONAD_XLA_' |
  grep -v '^__start_pb_defaults$' | grep -v '^__stop_pb_defaults$' || true)"
if [ -n "${exported}" ]; then
  echo "${library} exports more than monad_xla_*: ${exported}" >&2
  exit 1
fi
echo "Built ${library}"
if [ "${build_dir}" != "${repo_root}/build-xla" ]; then
  echo "Configure monad with -DMONAD_XLA_BUILD_DIR=${build_dir}"
fi
