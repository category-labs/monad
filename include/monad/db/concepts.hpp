#pragma once

#include <monad/db/config.hpp>

#include <concepts>

MONAD_DB_NAMESPACE_BEGIN

struct ReadOnly
{
};
struct ReadWrite
{
};

template <typename T>
concept Permission = std::same_as<T, ReadOnly> || std::same_as<T, ReadWrite>;

template <typename T>
concept Writable = std::same_as<T, ReadWrite>;

template <typename T>
concept Readable = std::same_as<T, ReadOnly> || std::same_as<T, ReadWrite>;

MONAD_DB_NAMESPACE_END
