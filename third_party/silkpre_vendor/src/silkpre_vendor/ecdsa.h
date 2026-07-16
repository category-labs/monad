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
//   - Rename to use monad prefixes
//   - Remove secp256k1_ecdh and related functions

#ifndef MONAD_ECDSA_H_
#define MONAD_ECDSA_H_

// See Yellow Paper, Appendix F "Signing Transactions"

#include <secp256k1.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

enum { MONAD_SECP256K1_CONTEXT_FLAGS = SECP256K1_CONTEXT_VERIFY };

//! \brief Tries recover the address used for message signing
//! \param [in] message : the signed message
//! \param [in] signature : the signature
//! \param [in] odd_y_parity : whether y parity is odd
//! \param [in] context: a pointer to an existing secp256k1 context
//! \return Whether the recovery has succeeded
bool monad_recover_address(uint8_t out[20], const uint8_t message[32], const uint8_t signature[64], bool odd_y_parity,
                           secp256k1_context* context);

#if defined(__cplusplus)
}
#endif

#endif  // MONAD_ECDSA_H_
