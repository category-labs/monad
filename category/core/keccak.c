#include <category/core/keccak.h>

#include <stddef.h>
#include <stdint.h>

#define BLOCK_SIZE ((1600 - 2 * 256) / 8)

extern size_t
SHA3_absorb(uint64_t A[5][5], unsigned char const *inp, size_t len, size_t r);

extern void
SHA3_squeeze(uint64_t A[5][5], unsigned char *out, size_t len, size_t r);

void keccak256(
    unsigned char const *const in, unsigned long const len,
    unsigned char out[KECCAK256_SIZE])
{
    uint64_t A[5][5];
    unsigned char blk[BLOCK_SIZE];

    __builtin_memset(A, 0, sizeof(A));

    size_t const rem = SHA3_absorb(A, in, len, BLOCK_SIZE);
    if (rem > 0) {
        __builtin_memcpy(blk, &in[len - rem], rem);
    }
    __builtin_memset(&blk[rem], 0, BLOCK_SIZE - rem);
    blk[rem] = 0x01;
    blk[BLOCK_SIZE - 1] |= 0x80;
    (void)SHA3_absorb(A, blk, BLOCK_SIZE, BLOCK_SIZE);

    SHA3_squeeze(A, out, 32, BLOCK_SIZE);
}
