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

#pragma once

#include <category/core/config.hpp>

#include <eip4844/eip4844.h>

#include <openssl/types.h>

MONAD_NAMESPACE_BEGIN

bool init_crypto();

// Preconditions for all accessors below: init_crypto() must have been called
// and returned true.
KZGSettings const &kzg_trusted_setup();
EVP_MD const *sha256_md();
EVP_MD const *ripemd160_md();

MONAD_NAMESPACE_END
