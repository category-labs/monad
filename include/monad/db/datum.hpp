#pragma once

#include <monad/core/address.hpp>
#include <monad/core/bytes.hpp>
#include <monad/db/config.hpp>

#include <optional>

MONAD_DB_NAMESPACE_BEGIN

namespace fnv1a
{
    static constexpr auto offset_basis = 14695981039346656037ull;
    static constexpr auto prime = 1099511628211ull;

    template <class T>
        requires requires(T const &b) { b.bytes; }
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

template <class T>
struct diff
{
    T const orig{};
    T updated{};

    diff() = default;
    diff(diff const &v) = default;
    diff(diff &&v) noexcept = default;
    diff(T const &o, T const &v)
        : orig{o}
        , updated{v}
    {
    }
    explicit diff(T const &v)
        : orig{}
        , updated{v}
    {
    }

    void operator=(T const &b) { updated = b; }

    struct equality
    {
        inline bool operator()(
            diff const &first, diff const &second) const noexcept
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
inline bool operator==(diff<T> const &a, T const &b) noexcept
{
    return a.updated == b;
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
