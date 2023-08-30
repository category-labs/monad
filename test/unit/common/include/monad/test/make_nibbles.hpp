#pragma once

#include <monad/test/config.hpp>
#include <monad/trie/nibbles.hpp>

#include <string>

MONAD_TEST_NAMESPACE_BEGIN

constexpr trie::Nibbles
make_nibbles(byte_string const &bytes, size_t size = std::string::npos)
{
    if ((bytes.size() * 2) <= size) {
        return trie::Nibbles{bytes};
    }
    else if ((size % 2) == 0) {
        return trie::Nibbles{bytes.substr(0, size / 2)};
    }
    MONAD_ASSERT(size <= std::numeric_limits<uint8_t>::max());
    return trie::Nibbles{
        trie::Nibbles{bytes}.prefix(static_cast<uint8_t>(size))};
}

MONAD_TEST_NAMESPACE_END
