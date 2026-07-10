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

#include "ecdsa.h"

#include <string.h>

#include <ethash/keccak.h>
#include <secp256k1_ecdh.h>
#include <secp256k1_recovery.h>

//! \brief Tries recover public key used for message signing.
//! \return An optional Bytes. Should it has no value the recovery has failed
//! This is different from recover_address as the whole 64 bytes are returned.
static bool recover(uint8_t public_key[65], const uint8_t message[32], const uint8_t signature[64], bool odd_y_parity,
                    secp256k1_context* context) {
    secp256k1_ecdsa_recoverable_signature sig;
    if (!secp256k1_ecdsa_recoverable_signature_parse_compact(context, &sig, signature, odd_y_parity)) {
        return false;
    }

    secp256k1_pubkey pub_key;
    if (!secp256k1_ecdsa_recover(context, &pub_key, &sig, message)) {
        return false;
    }

    size_t key_len = 65;
    secp256k1_ec_pubkey_serialize(context, public_key, &key_len, &pub_key, SECP256K1_EC_UNCOMPRESSED);
    return true;
}

//! Tries extract address from recovered public key
//! \param [in] public_key: The recovered public key
//! \return Whether the recovery has succeeded.
static bool public_key_to_address(uint8_t out[20], const uint8_t public_key[65]) {
    if (public_key[0] != 4u) {
        return false;
    }
    // Ignore first byte of public key
    const union ethash_hash256 key_hash = ethash_keccak256(public_key + 1, 64);
    memcpy(out, &key_hash.bytes[12], 20);
    return true;
}

bool silkpre_recover_address(uint8_t out[20], const uint8_t message[32], const uint8_t signature[64], bool odd_y_parity,
                             secp256k1_context* context) {
    uint8_t public_key[65];
    if (!recover(public_key, message, signature, odd_y_parity, context)) {
        return false;
    }
    return public_key_to_address(out, public_key);
}

// degenerate hash function that just copies the given X value
// see: ecies.GenerateShared in Erigon
static int ecdh_hash_function_copy_x(
    unsigned char *output,
    const unsigned char *x32,
    const unsigned char *y32,
    void *data) {

    memcpy(output, x32, 32);
    return 1;
};

bool silkpre_secp256k1_ecdh(
    const secp256k1_context* context,
    uint8_t* output,
    const secp256k1_pubkey* public_key,
    const uint8_t* private_key) {

    return secp256k1_ecdh(context, output, public_key, private_key, ecdh_hash_function_copy_x, NULL);
}
