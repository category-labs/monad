// evmone: Fast Ethereum Virtual Machine implementation
// Copyright 2022 The evmone Authors.
// SPDX-License-Identifier: Apache-2.0

// Modified 2026 by Category Labs:
//   - alt_bn128 (EIP-196 / EIP-197) precompiles from test/state/precompiles.cpp
//   - Rename to use monad prefixes
//   - Return success as bool and write the result to a caller-provided buffer

#pragma once

#include <cstddef>
#include <cstdint>

// EIP-196: Precompiled contract for addition on the elliptic curve alt_bn128
bool monad_bn_add(uint8_t out[64], uint8_t const *input, size_t len) noexcept;

// EIP-196: Precompiled contract for multiplication on the elliptic curve alt_bn128
bool monad_bn_mul(uint8_t out[64], uint8_t const *input, size_t len) noexcept;

// EIP-197: Precompiled contracts for optimal ate pairing check on the elliptic curve alt_bn128
bool monad_snarkv(uint8_t out[32], uint8_t const *input, size_t len) noexcept;
