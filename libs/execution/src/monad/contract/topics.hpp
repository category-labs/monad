#pragma once

#include <monad/config.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/cmemory.hpp>
#include <monad/core/keccak.hpp>

#include <string_view>
#include <vector>

MONAD_NAMESPACE_BEGIN

namespace detail
{

    template <typename T>
        requires(
            std::is_trivially_copyable_v<T> && sizeof(T) <= sizeof(bytes32_t))
    bytes32_t pad_to_bytes32(T const &value)
    {
        bytes32_t result{};
        std::memcpy(
            result.bytes + (sizeof(bytes32_t) - sizeof(T)), &value, sizeof(T));
        return result;
    }

}

template <typename... Args>
constexpr std::vector<bytes32_t>
create_topics(std::string_view event_signature, Args const &...args)
{
    static_assert(
        sizeof...(Args) <= 3, "Events can have at most 3 indexed parameters");
    std::vector<bytes32_t> topics;
    byte_string_view view{
        reinterpret_cast<uint8_t const *>(event_signature.data()),
        event_signature.size()};
    topics.emplace_back(to_bytes(keccak256(view)));
    (topics.emplace_back(detail::pad_to_bytes32(args)), ...);
    return topics;
}

MONAD_NAMESPACE_END
