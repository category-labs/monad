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

// Shared zkVM shadow of category/crypto/keccak.h. The host declares
// monad_keccak256() and defines it out of line over OpenSSL's SHA3 core; the
// guest takes the always_inline definition from the vendored ethash sponge
// instead, so the two cannot share a declaration. Everything else callers use
// from the host header is reproduced below.

#pragma once

// Include order matters: the vendored sponge calls monad_keccakf1600() without
// declaring it, so the backend's definition has to be in scope first.
#include <category/crypto/keccakf1600.h>

#include <category/crypto/ethash_vendor/keccak.h>

#include <stddef.h>

constexpr size_t KECCAK256_SIZE = 32;
