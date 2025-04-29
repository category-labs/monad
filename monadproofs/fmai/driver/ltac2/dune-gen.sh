#!/usr/bin/env bash
#
# dune-gen.sh: Generate Dune rules for all .cpp/.hpp in the current directory,
# using system include flags from ext_flags.sh

set -euo pipefail

# 1) Ensure dune.inc is cleared before writing
> dune.inc  # Truncate file (clear it)

# 2) Get the system flags by calling ext_flags.sh
# system_includes="$(./ext_flags.sh)"

# 3) Generate rules and write directly to dune.inc
shopt -s nullglob

for src in *.cpp *.hpp; do
    base="${src%.*}"   # e.g. foo.cpp -> foo
    ext="${src##*.}"   # e.g. foo.cpp -> cpp

    # Append the rule to dune.inc
    cat <<EOF >> dune.inc
(rule
 (targets ${base}.v)
 (alias test_ast)
 (deps (:input ${src}))
 (action
  (run cpp2v -v %{input} --no-elaborate -o ${base}.v
             -- -stdlib=libstdc++)))

(alias (name srcs) (deps ${src}))
EOF

done
