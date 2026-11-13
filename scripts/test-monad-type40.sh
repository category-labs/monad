#!/bin/sh
# Compile the actual codecs and static validators without building the full node.
set -eu
cd "$(dirname "$0")/.."
MONAD_TEST_BUILD_DIR=$(mktemp -d "${TMPDIR:-/tmp}/monad-type40.XXXXXX")
for src in category/crypto/keccak.c category/core/assert.c third_party/silkpre_vendor/src/category/crypto/silkpre_vendor/ecdsa.c; do
  "${CC:-clang-19}" -D_GNU_SOURCE -std=c23 -march=haswell -O1 -I. -Ithird_party/silkpre_vendor/src -c "$src" -o "${MONAD_TEST_BUILD_DIR}/$(basename "$src").o"
done
"${CC:-clang-19}" -march=haswell -Ithird_party/openssl -c category/crypto/keccak_impl.S -o "${MONAD_TEST_BUILD_DIR}/keccak_impl.o"
"${CXX:-clang++-19}" -std=c++26 -march=haswell -O1 -Wno-deprecated-declarations -ffunction-sections -fdata-sections -Wl,--gc-sections -I. -Ithird_party/asmjit/src -Ithird_party/cthash/include -Ithird_party/immer -Ithird_party/fiber/include -Ithird_party/concurrentqueue -Ithird_party/magic_enum/include -Ithird_party/unordered_dense/include -Ithird_party/nlohmann_json/include -Ithird_party/silkpre_vendor/src -Ithird_party/quill/include \
  category/execution/ethereum/core/rlp/transaction_rlp.cpp \
  category/execution/ethereum/core/rlp/receipt_rlp.cpp \
  category/execution/ethereum/core/rlp/signature_rlp.cpp \
  category/execution/ethereum/core/transaction.cpp \
  category/execution/ethereum/core/signature.cpp \
  category/execution/ethereum/core/ecrecover/impl.cpp \
  category/core/checked_math.cpp category/core/hex.cpp category/core/backtrace.cpp category/core/monad_exception.cpp category/core/rlp/decode_error.cpp \
  category/execution/ethereum/core/test/test_transaction_rlp.cpp \
  category/execution/ethereum/core/test/test_receipt_rlp.cpp \
  category/execution/ethereum/core/test/test_monad_transaction.cpp \
  category/execution/ethereum/core/test/test_monad_validation.cpp \
  category/execution/ethereum/validate_transaction.cpp \
  category/execution/ethereum/validate_transaction_error.cpp \
  category/execution/ethereum/transaction_gas.cpp \
  "${MONAD_TEST_BUILD_DIR}"/*.o -lsecp256k1 -lgtest -lgtest_main -lpthread -ldl -o "${MONAD_TEST_BUILD_DIR}/test_monad_transaction"
"${MONAD_TEST_BUILD_DIR}/test_monad_transaction"
