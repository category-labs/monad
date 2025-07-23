set +x
set -e
rm -rf build
CC=clang-19 CXX=clang++-19 cmake \
   -DCMAKE_TOOLCHAIN_FILE:STRING=libs/core/toolchains/gcc-avx2.cmake \
   -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
   -DCMAKE_BUILD_TYPE:STRING=RelWithDebInfo \
   -B build -G Ninja
./scripts/build.sh
DST=monadproofs/asts
CPP2V=../_build/install/default/bin/cpp2v
mkdir -p $DST
cp build/compile_commands.json ./ # cpp2v extracts the compile flags from here and passes the same to the clang AST visitor library
$CPP2V  ./libs/execution/src/monad/execution/execute_block.cpp --no-elaborate -o $(pwd)/$DST/exb.v # --templates exb_templates.v
$CPP2V  ./libs/execution/src/monad/execution/execute_transaction.cpp --no-elaborate -o $(pwd)/$DST/ext.v #-templates $(pwd)/$DST/ext_templates.v
$CPP2V ./libs/execution/src/monad/db/trie_db.hpp --no-elaborate -o $(pwd)/$DST/trie_db.v
$CPP2V ./libs/execution/src/monad/db/trie_rodb.hpp --no-elaborate -o $(pwd)/$DST/trie_rodb.v
$CPP2V  ./libs/execution/src/monad/state2/block_state.cpp --no-elaborate -o $(pwd)/$DST/block_state_cpp.v #-templates $(pwd)/$DST/block_state_templates.v
