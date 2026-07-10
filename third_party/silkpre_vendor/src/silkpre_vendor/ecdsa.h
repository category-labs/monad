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

#ifndef SILKPRE_ECDSA_H_
#define SILKPRE_ECDSA_H_

// See Yellow Paper, Appendix F "Signing Transactions"

#include <secp256k1.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

enum { SILKPRE_SECP256K1_CONTEXT_FLAGS = (SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY) };

//! \brief Tries recover the address used for message signing
//! \param [in] message : the signed message
//! \param [in] signature : the signature
//! \param [in] odd_y_parity : whether y parity is odd
//! \param [in] context: a pointer to an existing secp256k1 context
//! \return Whether the recovery has succeeded
bool silkpre_recover_address(uint8_t out[20], const uint8_t message[32], const uint8_t signature[64], bool odd_y_parity,
                             secp256k1_context* context);

bool silkpre_secp256k1_ecdh(
    const secp256k1_context* context,
    uint8_t* output,
    const secp256k1_pubkey* public_key,
    const uint8_t* private_key);

#if defined(__cplusplus)
}
#endif

#endif  // SILKPRE_ECDSA_H_
