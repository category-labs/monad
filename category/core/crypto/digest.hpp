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

#include <category/core/assert.h>
#include <category/core/config.hpp>

#include <openssl/evp.h>

#include <cstddef>
#include <cstdint>

MONAD_NAMESPACE_BEGIN

namespace detail
{
    struct DigestCtx
    {
        EVP_MD_CTX *const ptr;

        DigestCtx()
            : ptr(EVP_MD_CTX_new())
        {
            MONAD_ASSERT(ptr != nullptr);
        }

        ~DigestCtx()
        {
            EVP_MD_CTX_free(ptr);
        }

        DigestCtx(DigestCtx const &) = delete;
        DigestCtx &operator=(DigestCtx const &) = delete;
    };
}

// One thread-local context per digest type: each instantiation of `digest`
// has its own `thread_local` ctx, so OpenSSL's per-algorithm internal state
// (allocated on the first EVP_DigestInit_ex) is reused on subsequent calls
// instead of being torn down and re-allocated when alternating digests on a
// shared context. The template instantiation is shared across translation
// units, so callers in different files that pass the same MdGetter share a
// single per-thread context — and the `EVP_MD const *` returned by MdGetter
// is itself thread-safe to share globally; only the EVP_MD_CTX is per-thread.
//
// Fiber-safety invariant: this function MUST remain fiber-atomic. Boost.Fibers
// is cooperative and `thread_local` is keyed to the OS thread (not the
// fiber), so two fibers on the same thread alias the same DigestCtx. A yield
// between EVP_DigestInit_ex and EVP_DigestFinal_ex would let a co-scheduled
// fiber re-enter `digest<MdGetter>` and corrupt the in-flight state — and
// fiber migration to a different OS thread mid-digest would be even worse,
// since the resumed half would run against a different thread's context.
// Do not introduce any fiber yield point inside this function, and do not
// pass an MdGetter that can yield. Calls to `digest` themselves may safely
// be separated by yields; only the Init→Update→Final sequence inside one
// call must complete without yielding.
template <auto MdGetter>
void digest(
    uint8_t *const output, unsigned char const *const data, size_t const size)
{
    thread_local detail::DigestCtx ctx;

    // Some digest implementations invoke memcpy on the input buffer even
    // when the length is zero; swap a null data pointer for a pointer to
    // the empty string to stay out of UB.
    unsigned char const *const safe_data =
        data != nullptr ? data : reinterpret_cast<unsigned char const *>("");
    // EVP_DigestInit_ex re-initializes the context state when called on a
    // previously-used ctx, so we deliberately skip EVP_MD_CTX_reset.
    MONAD_ASSERT(EVP_DigestInit_ex(ctx.ptr, MdGetter(), nullptr) == 1);
    MONAD_ASSERT(EVP_DigestUpdate(ctx.ptr, safe_data, size) == 1);
    MONAD_ASSERT(EVP_DigestFinal_ex(ctx.ptr, output, nullptr) == 1);
}

MONAD_NAMESPACE_END
