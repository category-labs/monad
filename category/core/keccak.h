// Copyright (C) 2025 Category Labs, Inc.
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

#pragma once

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C"
{
#endif

constexpr size_t KECCAK256_SIZE = 32;

void keccak256(void const *in, size_t len, uint8_t out[KECCAK256_SIZE]);

// The Keccak-f memo that the guest can leave out does not exist here, so this
// is keccak256. The name exists because a translation unit shared with the
// guest calls it unguarded: in a cross build zkvm/category/core/keccak.h
// replaces this whole file and supplies the memo-free entry for real.
static inline void keccak256_nomemo(
    void const *const in, size_t const len, uint8_t out[KECCAK256_SIZE])
{
    keccak256(in, len, out);
}

#ifdef __cplusplus
}
#endif
