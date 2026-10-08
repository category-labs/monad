# Copyright (C) 2026 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, either version 3 of the License, or (at your option) any later
# version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program. If not, see <http://www.gnu.org/licenses/>.

# Shared L2 definitions. Root scope is required for ODR consistency of inline
# templates such as validate_ethereum_transaction. Deployment constants have
# no defaults: missing values must fail the build. MONAD_ZKVM_L2_CIPHER
# selects an implementation and has a default; its interface is in
# zkvm/guest/l2_cipher_suite.hpp.

# Cipher suites: add a name here, a selection arm in l2_cipher_suite.hpp, and
# sources/libraries in the helpers below. `plaintext` is a benchmark control
# using the same L2 rules without encryption; never deploy it.
set(MONAD_ZKVM_L2_CIPHERS ecdh-poseidon2 plaintext)

# MONAD_ZKVM_L2_HASH defaults to poseidon2 and selects block hashes, blooms,
# state blinders and their commitments. It also supplies the defaults for the
# independently selectable trie and signature hashes below. Configure host and
# guest identically. EVM hashing, code/contract addresses and namespace
# anchors remain Keccak.
set(MONAD_ZKVM_L2_HASHES keccak poseidon2)

# MONAD_ZKVM_L2_TRIE_HASH defaults to MONAD_ZKVM_L2_HASH and selects every
# Merkle-Patricia trie hash (category/core/trie_hash.hpp). Host and guest must
# agree or pre-state root verification fails.
set(MONAD_ZKVM_L2_TRIE_HASHES keccak poseidon2)

# MONAD_ZKVM_L2_SIGNATURE_HASH defaults to MONAD_ZKVM_L2_HASH and selects
# signing-digest and public-key address hashes (signature_hash.hpp). Keccak
# supports stock wallets; Poseidon2 requires a compatible signer.
set(MONAD_ZKVM_L2_SIGNATURE_HASHES keccak poseidon2)

set(MONAD_ZKVM_L2_REQUIRED
    MONAD_ZKVM_L2_CHAIN_ID
    MONAD_ZKVM_L2_REVISION
    MONAD_ZKVM_L2_SPOKE
    MONAD_ZKVM_L2_PENDING_SLOT
    MONAD_ZKVM_L2_OPERATOR_PK_X
    MONAD_ZKVM_L2_OPERATOR_PK_ODD
    MONAD_ZKVM_L2_SALT_COMMITMENT)

# Centralize suite sources and host libraries for both guest build modes and
# test registrations, so selecting a suite replaces all its dependencies.
function(monad_l2_cipher_sources GUEST_DIR OUT_VAR)
  if(NOT DEFINED MONAD_ZKVM_L2_CIPHER)
    set(MONAD_ZKVM_L2_CIPHER "ecdh-poseidon2")
  endif()

  if(MONAD_ZKVM_L2_CIPHER STREQUAL "ecdh-poseidon2")
    set(${OUT_VAR}
        "${GUEST_DIR}/l2_ecdh.cpp"
        "${GUEST_DIR}/l2_cipher.cpp"
        PARENT_SCOPE)
  elseif(MONAD_ZKVM_L2_CIPHER STREQUAL "plaintext")
    # Header-only: l2_plaintext_suite.hpp.
    set(${OUT_VAR} "" PARENT_SCOPE)
  else()
    # Catch a registered suite missing a source-list arm before link time.
    message(FATAL_ERROR
            "MONAD_ZKVM_L2_CIPHER='${MONAD_ZKVM_L2_CIPHER}' names no sources "
            "in monad_l2_cipher_sources; a suite added to "
            "MONAD_ZKVM_L2_CIPHERS needs an arm there too.")
  endif()
endfunction()

# The ECDH host backend uses the vendored secp256k1 target with ECDH enabled;
# ZisK uses zisklib. Link directly rather than relying on monad_execution's
# transitive dependency. Curveless suites add no library.
function(monad_l2_cipher_host_libs OUT_VAR)
  if(NOT DEFINED MONAD_ZKVM_L2_CIPHER)
    set(MONAD_ZKVM_L2_CIPHER "ecdh-poseidon2")
  endif()

  if(MONAD_ZKVM_L2_CIPHER STREQUAL "ecdh-poseidon2")
    set(${OUT_VAR} secp256k1 PARENT_SCOPE)
  else()
    set(${OUT_VAR} "" PARENT_SCOPE)
  endif()
endfunction()

# Guest sources: the selected suite plus shared L2 code. l2_sponge.cpp takes
# its domain label from the suite. Unselected suites are not compiled.
function(monad_l2_sources GUEST_DIR OUT_VAR)
  monad_l2_cipher_sources("${GUEST_DIR}" _suite)
  set(${OUT_VAR}
      ${_suite}
      "${GUEST_DIR}/l2_sponge.cpp"
      "${GUEST_DIR}/l2_config.cpp"
      "${GUEST_DIR}/domain_body.cpp"
      "${GUEST_DIR}/monad_l2_chain.cpp"
      PARENT_SCOPE)
endfunction()

# `0x` followed by exactly DIGITS hex digits, or a fatal error naming the value.
function(monad_l2_require_hex NAME DIGITS VALUE)
  string(LENGTH "${VALUE}" _len)
  math(EXPR _want "${DIGITS} + 2")
  if(NOT _len EQUAL _want OR NOT VALUE MATCHES "^0x[0-9a-fA-F]+$")
    message(FATAL_ERROR
            "${NAME} must be 0x followed by ${DIGITS} hex digits; got "
            "'${VALUE}' (${_len} characters)")
  endif()
endfunction()

function(monad_l2_compile_definitions)
  if(NOT DEFINED MONAD_ZKVM_L2_CIPHER)
    set(MONAD_ZKVM_L2_CIPHER "ecdh-poseidon2")
  endif()
  if(NOT DEFINED MONAD_ZKVM_L2_HASH)
    set(MONAD_ZKVM_L2_HASH "poseidon2")
  endif()
  if(NOT MONAD_ZKVM_L2_HASH IN_LIST MONAD_ZKVM_L2_HASHES)
    string(REPLACE ";" ", " _known "${MONAD_ZKVM_L2_HASHES}")
    message(FATAL_ERROR
            "MONAD_ZKVM_L2_HASH='${MONAD_ZKVM_L2_HASH}' is not a hash this "
            "tree implements; known: ${_known}.")
  endif()
  if(NOT DEFINED MONAD_ZKVM_L2_TRIE_HASH)
    set(MONAD_ZKVM_L2_TRIE_HASH "${MONAD_ZKVM_L2_HASH}")
  endif()
  if(NOT MONAD_ZKVM_L2_TRIE_HASH IN_LIST MONAD_ZKVM_L2_TRIE_HASHES)
    string(REPLACE ";" ", " _known "${MONAD_ZKVM_L2_TRIE_HASHES}")
    message(FATAL_ERROR
            "MONAD_ZKVM_L2_TRIE_HASH='${MONAD_ZKVM_L2_TRIE_HASH}' is not a trie "
            "hash this tree implements; known: ${_known}.")
  endif()
  if(NOT DEFINED MONAD_ZKVM_L2_SIGNATURE_HASH)
    set(MONAD_ZKVM_L2_SIGNATURE_HASH "${MONAD_ZKVM_L2_HASH}")
  endif()
  if(NOT MONAD_ZKVM_L2_SIGNATURE_HASH IN_LIST MONAD_ZKVM_L2_SIGNATURE_HASHES)
    string(REPLACE ";" ", " _known "${MONAD_ZKVM_L2_SIGNATURE_HASHES}")
    message(FATAL_ERROR
            "MONAD_ZKVM_L2_SIGNATURE_HASH='${MONAD_ZKVM_L2_SIGNATURE_HASH}' is "
            "not a signature hash this tree implements; known: ${_known}.")
  endif()
  # The L2 guest runs MonadTraits at MONAD_FOUR or later, where the reserve
  # balance tracks. State::push asserts that tracking is off when the dirty
  # account sets are gone, because dipped_into_reserve compares each frame's
  # accounts against their originals and has nothing to walk without them. An
  # ELF built with both halts at its first call frame -- and a ZisK halt is a
  # zero-filled output at rc=0, which reads like a run that merely disagreed.
  if(MONAD_ZKVM_NO_DIRTY_ACCOUNTS)
    message(FATAL_ERROR
            "MONAD_ZKVM_NO_DIRTY_ACCOUNTS is incompatible with MONAD_ZKVM_L2: "
            "the reserve balance needs the per-frame dirty account sets that "
            "lever removes, and the guest would halt on its first call.")
  endif()

  if(NOT MONAD_ZKVM_L2_CIPHER IN_LIST MONAD_ZKVM_L2_CIPHERS)
    string(REPLACE ";" ", " _known "${MONAD_ZKVM_L2_CIPHERS}")
    message(FATAL_ERROR
            "MONAD_ZKVM_L2_CIPHER='${MONAD_ZKVM_L2_CIPHER}' is not a suite "
            "this tree implements; known: ${_known}. Caught here rather than "
            "at the #error in l2_cipher_suite.hpp so the message can list "
            "them.")
  endif()

  set(_missing "")
  foreach(_v IN LISTS MONAD_ZKVM_L2_REQUIRED)
    if(NOT DEFINED ${_v})
      list(APPEND _missing ${_v})
    endif()
  endforeach()
  if(_missing)
    string(REPLACE ";" "\n  -D" _list "${_missing}")
    message(FATAL_ERROR
            "MONAD_ZKVM_L2 needs every deployment value spelled out; missing:"
            "\n  -D${_list}\n"
            "None has a default on purpose: a guest pointed at the wrong spoke "
            "or the wrong operator key emits proofs the L1 hub accepts.")
  endif()

  # CMake regexes lack brace repetition; check length and hex digits
  # separately.
  monad_l2_require_hex(MONAD_ZKVM_L2_SPOKE 40 "${MONAD_ZKVM_L2_SPOKE}")
  monad_l2_require_hex(
    MONAD_ZKVM_L2_OPERATOR_PK_X 64 "${MONAD_ZKVM_L2_OPERATOR_PK_X}")
  monad_l2_require_hex(
    MONAD_ZKVM_L2_SALT_COMMITMENT 64 "${MONAD_ZKVM_L2_SALT_COMMITMENT}")

  # The suite name reaches C++ as one macro per suite rather than as a string,
  # so the selection is a #if and an unselected suite is not compiled at all.
  string(TOUPPER "${MONAD_ZKVM_L2_CIPHER}" _cipher_upper)
  string(REPLACE "-" "_" _cipher_macro "${_cipher_upper}")
  string(TOUPPER "${MONAD_ZKVM_L2_HASH}" _hash_macro)
  string(TOUPPER "${MONAD_ZKVM_L2_TRIE_HASH}" _trie_hash_macro)
  string(TOUPPER "${MONAD_ZKVM_L2_SIGNATURE_HASH}" _signature_hash_macro)

  # The address and the x-coordinate arrive as user-defined literals, so the
  # header needs no hex parser of its own.
  add_compile_definitions(
    MONAD_ZKVM_L2
    MONAD_L2_CIPHER_${_cipher_macro}
    MONAD_L2_HASH_${_hash_macro}
    MONAD_L2_TRIE_HASH_${_trie_hash_macro}
    MONAD_L2_SIGNATURE_HASH_${_signature_hash_macro}
    MONAD_L2_CHAIN_ID=${MONAD_ZKVM_L2_CHAIN_ID}
    MONAD_L2_REVISION=${MONAD_ZKVM_L2_REVISION}
    MONAD_L2_DOMAIN_SPOKE=${MONAD_ZKVM_L2_SPOKE}_address
    MONAD_L2_PENDING_SLOT=${MONAD_ZKVM_L2_PENDING_SLOT}
    MONAD_L2_OPERATOR_PK_X=${MONAD_ZKVM_L2_OPERATOR_PK_X}_bytes32
    MONAD_L2_OPERATOR_PK_ODD=${MONAD_ZKVM_L2_OPERATOR_PK_ODD}
    MONAD_L2_SALT_COMMITMENT=${MONAD_ZKVM_L2_SALT_COMMITMENT}_bytes32)
endfunction()
