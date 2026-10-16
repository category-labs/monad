// The guest's keccak at every offset in an 8-byte word against the same bytes
// hashed from an aligned copy, lengths 0 to 700: the sponge has separate paths
// for aligned and misaligned input. Linked in place of the guest's entry
// (keccak_align_test.sh); the output words are the checks, the failures,
// the first failing (offset << 16 | length) and a fold of every digest.
#include <cstddef>
#include <cstdint>
#include <cstring>

extern "C" void write_output(uint8_t const *output, size_t size);
extern "C" void monad_zkvm_keccak256_fast(void const *in, size_t len, uint8_t out[32]);

alignas(64) static uint8_t src[1024];
alignas(64) static uint8_t aligned[1024];

extern "C" void monad_zkvm_execute_witness()
{
    uint64_t state = 0x9e3779b97f4a7c15ull;
    for (auto &b : src) {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        b = static_cast<uint8_t>(state);
    }
    uint32_t checks = 0, failures = 0, first = 0xffffffff;
    // Every digest folded in: equal across two builds, the two sponges agree
    // on all of them.
    uint32_t fold[8] = {};
    for (uint32_t off = 0; off < 8; ++off) {
        for (uint32_t len = 0; len <= 700; ++len) {
            uint8_t a[32], b[32];
            monad_zkvm_keccak256_fast(src + off, len, a);
            for (int i = 0; i < 8; ++i) {
                uint32_t v;
                std::memcpy(&v, a + 4 * i, 4);
                fold[i] = (fold[i] ^ v) * 0x9e3779b1u + static_cast<uint32_t>(i);
            }
            std::memcpy(aligned, src + off, len);
            monad_zkvm_keccak256_fast(aligned, len, b);
            if (std::memcmp(a, b, 32) != 0 && failures++ == 0) {
                first = off << 16 | len;
            }
            ++checks;
        }
    }
    uint32_t const out[11] = {checks, failures, first, fold[0], fold[1],
                              fold[2], fold[3], fold[4], fold[5], fold[6],
                              fold[7]};
    write_output(reinterpret_cast<uint8_t const *>(out), sizeof(out));
}
