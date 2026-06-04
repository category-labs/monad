// Copyright (C) 2025-26 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// Shared zkVM shadow of category/core/keccak.h. Forwards keccak256(in, len,
// out) to the standardized zkVM accelerator API (zkvm/core/zkvm_accelerators.h
// :: zkvm_keccak256), which both ZisK and SP1 expose as `extern "C"` link-time
// symbols (ZisK provides it natively in zisklib; SP1 has a Rust shim in
// zkvm/sp1/program/src/main.rs).

#pragma once

#include <zkvm/core/zkvm_accelerators.h>

#define KECCAK256_SIZE 32

#ifdef __cplusplus
extern "C"
{
#endif

[[gnu::always_inline]] static inline void keccak256(
    unsigned char const *const in, unsigned long const len,
    unsigned char out[KECCAK256_SIZE])
{
    zkvm_keccak256(in, (size_t)len, (zkvm_keccak256_hash *)out);
}

#ifdef __cplusplus
}
#endif
