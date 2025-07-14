#include <category/core/rlp/encode.hpp>

#include <category/core/rlp/config.hpp>

#include <category/core/byte_string.hpp>

#include <cstddef>
#include <span>

MONAD_RLP_NAMESPACE_BEGIN

namespace impl
{
    size_t length_length_disas(size_t const n)
    {
        return length_length(n);
    }

    std::span<unsigned char>
    encode_length_disas(std::span<unsigned char> const d, size_t const n)
    {
        return encode_length(d, n);
    }
}

size_t string_length_disas(byte_string_view const s)
{
    return string_length(s);
}

std::span<unsigned char>
encode_string_disas(std::span<unsigned char> const d, byte_string_view const s)
{
    return encode_string(d, s);
}

size_t list_length_disas(size_t const concatenated_size)
{
    return list_length(concatenated_size);
}

std::span<unsigned char>
encode_list_disas(std::span<unsigned char> const d, byte_string_view const s)
{
    return encode_list(d, s);
}

MONAD_RLP_NAMESPACE_END
