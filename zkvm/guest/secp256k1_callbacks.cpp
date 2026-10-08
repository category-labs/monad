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

// libsecp256k1's default callbacks, for a target with no stdio. Its own print
// to stderr and abort, which drags in fprintf and newlib's _impure_ptr; the
// guest is built with USE_EXTERNAL_DEFAULT_CALLBACKS so that these stand in.
//
// Both still end the run, and that is the point. An illegal argument is a
// caller's bug and an internal check failing is the library's: neither is a
// state transition, so continuing would prove something about a computation
// that did not happen.

#include <category/core/assert.h>

extern "C" {

void secp256k1_default_illegal_callback_fn(char const *str, void *data);
void secp256k1_default_error_callback_fn(char const *str, void *data);

// MONAD_ABORT takes a constant message, so the library's own string is not
// passed on. The two cases are distinguished instead, which is what tells a
// caller's bug from the library's.
void secp256k1_default_illegal_callback_fn(char const *, void *)
{
    MONAD_ABORT("libsecp256k1: illegal argument");
}

void secp256k1_default_error_callback_fn(char const *, void *)
{
    MONAD_ABORT("libsecp256k1: internal consistency check failed");
}
}
