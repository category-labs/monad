/*
   Copyright 2022 The Silkpre Authors

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

// Modified 2026 by Category Labs:
//   - alt_bn128 (EIP-196 / EIP-197) precompiles from silkpre/precompile.cpp
//   - Rename to use monad prefixes
//   - Return the result in a caller-provided buffer instead of SilkpreOutput

#pragma once

#include <cstddef>
#include <cstdint>

// EIP-196: Precompiled contract for addition on the elliptic curve alt_bn128
bool monad_bn_add(uint8_t out[64], const uint8_t *input, size_t len);

// EIP-196: Precompiled contract for multiplication on the elliptic curve alt_bn128
bool monad_bn_mul(uint8_t out[64], const uint8_t *input, size_t len);

// EIP-197: Precompiled contracts for optimal ate pairing check on the elliptic curve alt_bn128
bool monad_snarkv(uint8_t out[32], const uint8_t *input, size_t len);
