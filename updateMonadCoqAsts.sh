set +x
set -e
rm -rf build
CC=clang-18 CXX=clang++-18 cmake \
    -DCMAKE_TOOLCHAIN_FILE:STRING=libs/core/toolchains/gcc-avx2.cmake \
    -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
    -DCMAKE_BUILD_TYPE:STRING=RelWithDebInfo \
    -B build -G Ninja
./scripts/build.sh
DST=monadproofs/asts
CPP2V=../_build/install/default/bin/cpp2v
mkdir -p $DST
cp build/compile_commands.json ./ # cpp2v extracts the compile flags from here and passes the same to the clang AST visitor library
$CPP2V  ./libs/execution/src/monad/execution/execute_block.cpp --no-elaborate -o $(pwd)/$DST/exb.v
$CPP2V  ./libs/execution/src/monad/execution/execute_transaction.cpp --no-elaborate -o $(pwd)/$DST/ext.v
$CPP2V  ./libs/execution/src/monad/state2/block_state.cpp --no-elaborate -o $(pwd)/$DST/block_state_cpp.v
