#pragma once

#ifdef __cplusplus
extern "C"
{
#endif

#define KECCAK256_SIZE 32

void keccak256(
    unsigned char const *in, unsigned long len,
    unsigned char out[KECCAK256_SIZE]);

#ifdef __cplusplus
}
#endif
