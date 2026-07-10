/*
   BLAKE2 reference source code package - reference C implementations

   Copyright 2012, Samuel Neves <sneves@dei.uc.pt>.  You may use this under the
   terms of the CC0, the OpenSSL Licence, or the Apache Public License 2.0, at
   your option.  The terms of these licenses can be found at:

   - CC0 1.0 Universal : http://creativecommons.org/publicdomain/zero/1.0
   - OpenSSL license   : https://www.openssl.org/source/license.html
   - Apache 2.0        : http://www.apache.org/licenses/LICENSE-2.0

   More information about the BLAKE2 hash function can be found at
   https://blake2.net.

   Modified 2022 for Silkpre by Andrew Ashikhmin.
*/

#ifndef SILKPRE_BLAKE2B_H_
#define SILKPRE_BLAKE2B_H_

#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

enum { SILKPRE_BLAKE2B_BLOCKBYTES = 128 };

typedef struct SilkpreBlake2bState {
    uint64_t h[8];
    uint64_t t[2];
    uint64_t f[2];
} SilkpreBlake2bState;

// https://tools.ietf.org/html/rfc7693#section-3.2
void silkpre_blake2b_compress(SilkpreBlake2bState* S, const uint8_t block[SILKPRE_BLAKE2B_BLOCKBYTES], size_t r);

#if defined(__cplusplus)
}
#endif

#endif  // SILKPRE_BLAKE2B_H_
