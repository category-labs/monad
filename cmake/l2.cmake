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

# MONAD_ZKVM_L2's definitions, in one place because they have to be emitted in
# three directory scopes.
#
# The root scope is not optional, and the reason is an ODR rule rather than
# convenience: validate_ethereum_transaction is an always-inline function
# template in validate_transaction.hpp, consumed by several translation units.
# A macro visible to one and not another would be a one-definition-rule
# violation on that inline, with no diagnostic.
#
# Every deployment value is REQUIRED and has no default. A guest that anchors
# the wrong contract, or decrypts under the wrong operator key, produces a proof
# the L1 hub accepts -- so a missing value has to stop the build, not pick
# something plausible.
#
# MONAD_ZKVM_L2_CIPHER is the exception and does have a default, because it
# names an implementation rather than a deployment: getting it wrong cannot
# produce a proof of the wrong thing, it produces leaves that do not decrypt.
# It is the seam the encryption is swapped at -- see
# zkvm/guest/l2_cipher_suite.hpp, which holds the interface a suite must
# provide and the concept that checks it.

# Every suite this build knows. A suite is a type satisfying L2CipherSuite plus
# the sources implementing it; adding one means a name here, a #if arm in
# l2_cipher_suite.hpp, and its sources in _l2_sources in
# zkvm/guest/CMakeLists.txt. The macro is derived from the name below, so there
# is nothing to keep in step by hand, and nothing in the proved path changes at
# all -- it names no cipher.
set(MONAD_ZKVM_L2_CIPHERS ecdh-poseidon2)

set(MONAD_ZKVM_L2_REQUIRED
    MONAD_ZKVM_L2_CHAIN_ID
    MONAD_ZKVM_L2_NAMESPACE_ID
    MONAD_ZKVM_L2_REVISION
    MONAD_ZKVM_L2_SPOKE
    MONAD_ZKVM_L2_PENDING_SLOT
    MONAD_ZKVM_L2_OPERATOR_PK_X
    MONAD_ZKVM_L2_OPERATOR_PK_ODD
    MONAD_ZKVM_L2_EPOCH_BLOCKS)

# What the SELECTED suite is made of: its sources, and the host libraries its
# off-ZisK arm needs. Everything suite-specific in the build is these two
# lists, so adding a suite is an arm in each and nothing else.
#
# Here rather than in zkvm/guest/CMakeLists.txt because that file needs them in
# both of its branches -- the cross-compile one and the host-x86 one, which see
# none of each other's variables -- and in four test registrations besides.
# Copies of a list that decides what a suite is made of is how a suite comes to
# be half-swapped.
function(monad_l2_cipher_sources GUEST_DIR OUT_VAR)
  if(NOT DEFINED MONAD_ZKVM_L2_CIPHER)
    set(MONAD_ZKVM_L2_CIPHER "ecdh-poseidon2")
  endif()

  if(MONAD_ZKVM_L2_CIPHER STREQUAL "ecdh-poseidon2")
    set(${OUT_VAR}
        "${GUEST_DIR}/l2_ecdh.cpp"
        "${GUEST_DIR}/l2_cipher.cpp"
        PARENT_SCOPE)
  else()
    # Unreachable: monad_l2_compile_definitions rejects an unknown name, and it
    # runs first. Said out loud so a suite added to MONAD_ZKVM_L2_CIPHERS
    # without an arm here fails on a message rather than on a link error
    # naming a mangled symbol.
    message(FATAL_ERROR
            "MONAD_ZKVM_L2_CIPHER='${MONAD_ZKVM_L2_CIPHER}' names no sources "
            "in monad_l2_cipher_sources; a suite added to "
            "MONAD_ZKVM_L2_CIPHERS needs an arm there too.")
  endif()
endfunction()

# libsecp256k1 is the ECDH suite's HOST arm only -- on ZisK the same code goes
# through ziskos' zisklib and links nothing. category/execution links it
# PRIVATE, so a target using that arm has to name it itself. A suite with no
# curve returns an empty list and the target links nothing extra.
function(monad_l2_cipher_host_libs OUT_VAR)
  if(NOT DEFINED MONAD_ZKVM_L2_CIPHER)
    set(MONAD_ZKVM_L2_CIPHER "ecdh-poseidon2")
  endif()

  if(MONAD_ZKVM_L2_CIPHER STREQUAL "ecdh-poseidon2")
    set(${OUT_VAR} PkgConfig::secp256k1 PARENT_SCOPE)
  else()
    set(${OUT_VAR} "" PARENT_SCOPE)
  endif()
endfunction()

# Every guest source an L2 build compiles: the selected suite's, plus the ones
# no suite owns. l2_sponge.cpp is shared because it carries no protocol
# identity of its own -- it takes its domain label from the suite, so two
# suites over the same permutation are still separated oracles.
#
# Only the selected suite is named, so an unselected one costs nothing: no
# instructions, no bytes, no static initialisers.
function(monad_l2_sources GUEST_DIR OUT_VAR)
  monad_l2_cipher_sources("${GUEST_DIR}" _suite)
  set(${OUT_VAR}
      ${_suite}
      "${GUEST_DIR}/l2_sponge.cpp"
      "${GUEST_DIR}/l2_config.cpp"
      "${GUEST_DIR}/decode_block_l2.cpp"
      "${GUEST_DIR}/monad_l2_chain.cpp"
      PARENT_SCOPE)
endfunction()

# The two DIAGNOSTIC levers, both OFF by default and neither ever part of a
# provable configuration. They exist so the corpus differential can run on the
# witnesses that exist rather than on the ones its design assumed.
#
# MONAD_ZKVM_L2_ALLOW_L1_SHAPE accepts a block shape the L2 has no rules for --
# withdrawals, a present requests_hash, blob transactions -- and IGNORES what
# it cannot authenticate rather than implementing it. It creates no balance:
# the epilogue still skips process_withdrawal, so the P1 it reaches into stays
# closed even here.
#
# MONAD_ZKVM_L2_PLAINTEXT_LEAVES is the differential's reference arm: L2 chain,
# L2 gas rules, L2 block shape, L2 anchor, but a six-field witness whose leaves
# are plaintext. Both arms of the differential are L2 builds and differ only in
# this, which is what makes the comparison an argument about the cipher.
# Comparing against a non-L2 build compares two rule sets instead: gas is
# priced there, so the sender's balance, the refund and the beneficiary's tips
# move on one arm and not the other, and the roots differ on every block that
# has a transaction.
function(monad_l2_diagnostic_definitions)
  if(MONAD_ZKVM_L2_ALLOW_L1_SHAPE)
    add_compile_definitions(MONAD_ZKVM_L2_ALLOW_L1_SHAPE)
    message(WARNING
            "MONAD_ZKVM_L2_ALLOW_L1_SHAPE: this guest accepts withdrawals, a "
            "requests hash and blob transactions that it has no rules for, and "
            "ignores them. Diagnostic only -- the roots it commits describe no "
            "chain. Nothing built this way should be proved or published.")
  endif()
  if(MONAD_ZKVM_L2_PLAINTEXT_LEAVES)
    add_compile_definitions(MONAD_ZKVM_L2_PLAINTEXT_LEAVES)
    message(WARNING
            "MONAD_ZKVM_L2_PLAINTEXT_LEAVES: this guest does not decrypt. It "
            "is the corpus differential's reference arm and proves nothing "
            "about the cipher on its own -- only the pair does.")
  endif()
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

  # Length and character class checked separately, because CMake's regex
  # engine has no brace repetition: "[0-9a-fA-F]{40}" matches nothing at all,
  # so a guard written that way rejects every value it was meant to accept and
  # the option can never be set. Found by configuring.
  monad_l2_require_hex(MONAD_ZKVM_L2_SPOKE 40 "${MONAD_ZKVM_L2_SPOKE}")
  monad_l2_require_hex(
    MONAD_ZKVM_L2_OPERATOR_PK_X 64 "${MONAD_ZKVM_L2_OPERATOR_PK_X}")

  # The suite name reaches C++ as one macro per suite rather than as a string,
  # so the selection is a #if and an unselected suite is not compiled at all.
  string(TOUPPER "${MONAD_ZKVM_L2_CIPHER}" _cipher_upper)
  string(REPLACE "-" "_" _cipher_macro "${_cipher_upper}")

  # The address and the x-coordinate arrive as user-defined literals, so the
  # header needs no hex parser of its own.
  add_compile_definitions(
    MONAD_ZKVM_L2
    MONAD_L2_CIPHER_${_cipher_macro}
    MONAD_L2_CHAIN_ID=${MONAD_ZKVM_L2_CHAIN_ID}
    MONAD_L2_NAMESPACE_ID=${MONAD_ZKVM_L2_NAMESPACE_ID}
    MONAD_L2_REVISION=${MONAD_ZKVM_L2_REVISION}
    MONAD_L2_NAMESPACE_SPOKE=${MONAD_ZKVM_L2_SPOKE}_address
    MONAD_L2_PENDING_SLOT=${MONAD_ZKVM_L2_PENDING_SLOT}
    MONAD_L2_OPERATOR_PK_X=${MONAD_ZKVM_L2_OPERATOR_PK_X}_bytes32
    MONAD_L2_OPERATOR_PK_ODD=${MONAD_ZKVM_L2_OPERATOR_PK_ODD}
    MONAD_L2_EPOCH_BLOCKS=${MONAD_ZKVM_L2_EPOCH_BLOCKS})

  monad_l2_diagnostic_definitions()
endfunction()
