#pragma once

#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>

MONAD_DB_NAMESPACE_BEGIN

namespace fnv1a
{
    static constexpr auto offset_basis = 14695981039346656037ull;
    static constexpr auto prime = 1099511628211ull;

    template <class T>
    static constexpr inline auto hash(T const &b) noexcept
    {
        uint64_t h = offset_basis;
        for (auto i = 0u; i < sizeof(b.bytes); ++i) {
            h ^= b.bytes[i];
            h *= prime;
        }
        return h;
    }
}

namespace city_hash
{
    static constexpr auto k0 = 0xc3a5c85c97cb3127ull;
    static constexpr auto k1 = 0xb492b66fbe98f273ull;

    static inline auto hash(bytes32_t const &b) noexcept
    {
        auto data = reinterpret_cast<const uint64_t *>(b.bytes);
        constexpr auto len = 4;

        auto h = len + k1;
        auto g = h;
        auto f = 0ull;

        for (uint64_t i = 0; i < 2; ++i) {
            uint64_t v = *data++;
            f = v * k0;
            g = ((g * k1) + (f << 37) | (f >> 27)) * k1;
            h ^= g;
            h = ((h << 27) | (h >> 37)) * 5 + 0x52dce729;
        }

        h ^= b.bytes[0];
        h ^= b.bytes[1];
        h ^= (h >> 23);
        h *= 0x2127599bf4325c37ULL;
        h ^= (h >> 47);

        return h;
    }
}

template <class T>
struct diff_value
{
    T const orig{};
    T value{};

    diff_value() = default;
    diff_value(diff_value const &v) = default;
    diff_value(diff_value &&v) noexcept = default;
    diff_value(T const &o, T const &v)
        : orig{o}
        , value{v}
    {
    }
    explicit diff_value(T const &v)
        : orig{}
        , value{v}
    {
    }

    // void operator=(diff_value const &v) { orig = v.orig; value = v.value; }
    void operator=(T const &b) { value = b; }
    void operator=(T &&b) { value = std::move(b); }

    struct equality
    {
        inline bool operator()(
            diff_value const &first, diff_value const &second) const noexcept
        {
            return first.value == second.value;
        }
    };

    struct hash
    {
        constexpr inline std::size_t operator()(T const &a) const
        {
            return fnv1a::hash(a);
        }
    };
};

template <class T>
inline bool operator==(diff_value<T> const &a, T const &b) noexcept
{
    return a.value == b;
}

struct deleted_key
{
    bytes32_t const orig_value{};
    bytes32_t key{};

    deleted_key() = default;
    deleted_key(deleted_key const &v) = default;
    deleted_key(deleted_key &&v) noexcept = default;
    explicit deleted_key(bytes32_t const &k)
        : orig_value{}
        , key{k}
    {
    }
    deleted_key(bytes32_t const &b, bytes32_t const &k)
        : orig_value{b}
        , key{k}
    {
    }

    // void operator=(deleted_key const &d) { key = d.key; }
    void operator=(bytes32_t const &b) { key = b; }

    struct equality
    {
        inline bool operator()(
            deleted_key const &first, deleted_key const &second) const noexcept
        {
            return first.key == second.key;
        }
    };

    struct hash
    {
        constexpr inline std::size_t operator()(deleted_key const &d) const
        {
            return fnv1a::hash(d.key);
        }
    };
};

inline bool operator==(deleted_key const &a, bytes32_t const &b) noexcept
{
    return a.key == b;
}

MONAD_DB_NAMESPACE_END
