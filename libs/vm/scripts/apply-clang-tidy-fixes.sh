#!/bin/bash

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

if [[ ! -z "$(git status --untracked-files=no --porcelain)" ]]; then
  printf "FATAL: Do not run this on a git repo with uncommitted changes\n\n\n" >&2
  git status --untracked-files=no
  exit 1
fi

BUILDDIR=$1/
shift

RUN_CLANG_TIDY="$1"
shift

if [ -z "$RUN_CLANG_TIDY" ]; then
  RUN_CLANG_TIDY=run-clang-tidy
fi

if [[ -z "$1" && -f "build/compile_commands.json" ]]; then
  BUILDDIR=build/
fi
if [[ -z "$1" && -f "compile_commands.json" ]]; then
  BUILDDIR=
fi
if [[ ! -f "${BUILDDIR}compile_commands.json" ]]; then
  echo "FATAL:Pass the path to the cmake build directory containing 'compile_commands.json' as the first argument" >&2
  exit 1
fi

"${SCRIPT_DIR}/check-clang-tidy.sh" \
  --build-dir "${BUILDDIR}"         \
  --driver "${RUN_CLANG_TIDY}"      \
  -- -fix -format | tee "${BUILDDIR}/apply-clang-tidy-fixes.log"

if [[ ! -z "$(git status --untracked-files=no --porcelain)" ]]; then
  git status --untracked-files=no
  printf "\nFixes were applied, make sure everything compiles and works then do 'git commit --amend'\n"
else
  printf "\nNo fixes applied, you don't need to run 'git commit --amend'\n"
fi
printf "\nA copy of the output above has been placed into '${BUILDDIR}apply-clang-tidy-fixes.log'\n"
