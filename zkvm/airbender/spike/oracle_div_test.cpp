// Host-quotient division on Airbender against the software Knuth division:
// udivrem, sdivrem, mulmod and addmod over edge values and pseudo-random
// operands of every width, run in the VM by zkvm/airbender/runner. Links in
// place of the guest's entry (see oracle_div_test.sh); the output words are
// the checks run, the failures, and the first failure's case number.
#include <category/core/runtime/uint256.hpp>

#include <cstddef>
#include <cstdint>

extern "C" void write_output(uint8_t const *output, size_t size);

using monad::uint256_t;
using monad::words_t;

namespace
{
    uint64_t state = 0x9e3779b97f4a7c15ull;

    uint64_t next()
    {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        return state;
    }

    // Values of every width: random words above a random bit length, or one
    // of the edges (powers of two, one less, all ones).
    uint256_t value()
    {
        uint64_t const pick = next();
        unsigned const bits = static_cast<unsigned>(pick % 257);
        switch ((pick >> 9) % 8) {
        case 0:
            return bits == 256 ? uint256_t{0} : uint256_t{1} << bits;
        case 1:
            return (bits == 256 ? uint256_t{0} : uint256_t{1} << bits) - 1;
        case 2:
            return uint256_t{next() & 7};
        default: {
            uint256_t x{next(), next(), next(), next()};
            return bits == 0 ? uint256_t{0} : x >> (256 - bits);
        }
        }
    }

    uint256_t reference_rem(words_t<8> const &u, uint256_t const &m)
    {
        return uint256_t{monad::udivrem(u, m.as_words()).rem};
    }

    uint32_t checks = 0;
    uint32_t failures = 0;
    uint32_t first_failure = 0xffffffff;

    void check(bool const ok)
    {
        if (!ok && failures++ == 0) {
            first_failure = checks;
        }
        ++checks;
    }
}

// Operands where the circuit can read them in place (32-byte aligned) and
// where they must be copied first (8 bytes past that).
struct Placed
{
    alignas(32) uint256_t aligned[3];
    uint64_t pad;
    uint256_t misaligned[3];
};

Placed placed;

extern "C" void monad_zkvm_execute_witness()
{
    for (int i = 0; i < 8000; ++i) {
        uint256_t *const at = (i & 1) ? placed.misaligned : placed.aligned;
        at[0] = value();
        at[1] = value();
        at[2] = value();
        uint256_t const &u = at[0];
        uint256_t const &v = at[1];
        uint256_t const &m = at[2];
        if (v != 0) {
            auto const got = monad::udivrem(u, v);
            auto const want = monad::udivrem(u.as_words(), v.as_words());
            check(
                got.quot == uint256_t{want.quot} &&
                got.rem == uint256_t{want.rem});
            auto const s = monad::sdivrem(u, v);
            check(s.quot * v + s.rem == u);
        }
        if (m != 0) {
            auto const prod =
                monad::truncating_mul<8>(u.as_words(), v.as_words());
            check(monad::mulmod(u, v, m) == reference_rem(prod, m));
            words_t<8> sum{};
            uint64_t carry = 0;
            for (size_t w = 0; w < 4; ++w) {
                auto const [s, c] = monad::addc(u[w], v[w], carry);
                sum[w] = s;
                carry = c;
            }
            sum[4] = carry;
            check(monad::addmod(u, v, m) == reference_rem(sum, m));
        }
    }
    uint32_t const out[3] = {checks, failures, first_failure};
    write_output(reinterpret_cast<uint8_t const *>(out), sizeof(out));
}
