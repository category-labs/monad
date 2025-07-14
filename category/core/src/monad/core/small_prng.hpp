#pragma once

#include "../config.hpp"

#include <cstddef>
#include <cstdint>

#include <unistd.h> // for gettid()

MONAD_NAMESPACE_BEGIN

/*! \class small_prng
\brief From http://burtleburtle.net/bob/rand/smallprng.html, a not awful fast
random number source.
*/
class small_prng
{
protected:
    uint32_t a;
    uint32_t b;
    uint32_t c;
    uint32_t d;

    static constexpr uint32_t rot(uint32_t x, uint32_t k) noexcept
    {
        return (((x) << (k)) | ((x) >> (32 - (k))));
    }

public:
    //! The type produced by the small prng
    using value_type = uint32_t;

    // To make this directly usable with `std::shuffle()`
    using result_type = uint32_t;
    static constexpr result_type min()
    {
        return 0;
    }
    static constexpr result_type max()
    {
        return UINT32_MAX;
    }

    //! Construct an instance with `seed`
    explicit constexpr small_prng(uint32_t seed = 0xdeadbeef) noexcept
        : a{0xf1ea5eed}
        , b(seed)
        , c(seed)
        , d(seed)
    {
        for (size_t i = 0; i < 20; ++i) {
            (*this)();
        }
    }

    //! Return `value_type` of pseudo-randomness
    constexpr uint32_t operator()() noexcept
    {
        uint32_t const e = a - rot(b, 27);
        a = b ^ rot(c, 17);
        b = c + d;
        c = d + e;
        d = e + a;
        return d;
    }
};

//! \brief A thread safe small prng seeded with the thread id
inline small_prng &thread_local_prng()
{
    static thread_local small_prng v(static_cast<uint32_t>(gettid()));
    return v;
}

//! A `random_shuffle` implementation which uses the small prng
template <class RandomIt>
void random_shuffle(
    RandomIt first, RandomIt last, small_prng &r = thread_local_prng())
{
    typename std::iterator_traits<RandomIt>::difference_type i, n;
    n = last - first;
    for (i = n - 1; i > 0; --i) {
        using std::swap;
        swap(first[i], first[r() % (i + 1)]);
    }
}

MONAD_NAMESPACE_END
