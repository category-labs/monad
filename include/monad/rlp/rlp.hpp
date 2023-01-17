#pragma once

#include <cassert>
#include <concepts>
#include <intx/intx.hpp>
#include <limits>
#include <monad/config.hpp>
#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/likely.h>
#include <type_traits>

MONAD_NAMESPACE_BEGIN

// https://ethereum.org/en/developers/docs/data-structures-and-encoding/rlp/
//
// RLP encoding is defined as follows:
//
//  For a single byte whose value is in the [0x00, 0x7f] (decimal [0,
//  127]) range, that byte is its own RLP encoding.
//
//  Otherwise, if a string is 0-55 bytes long, the RLP encoding consists
//  of a single byte with value 0x80 (dec. 128) plus the length of the
//  string followed by the string. The range of the first byte is thus
//  [0x80, 0xb7] (dec. [128, 183]).
//
//  If a string is more than 55 bytes long, the RLP encoding consists of
//  a single byte with value 0xb7 (dec. 183) plus the length in bytes of
//  the length of the string in binary form, followed by the length of
//  the string, followed by the string. For example, a 1024 byte long
//  string would be encoded as \xb9\x04\x00 (dec. 185, 4, 0) followed
//  by the string. Here, 0xb9 (183 + 2 = 185) as the first byte,
//  followed by the 2 bytes 0x0400 (dec. 1024) that denote the length
//  of the actual string. The range of the first byte is thus
//  [0xb8, 0xbf] (dec. [184, 191]).
//
//  If the total payload of a list (i.e. the combined length of all its
//  items being RLP encoded) is 0-55 bytes long, the RLP encoding
//  consists of a single byte with value 0xc0 plus the length of the
//  list followed by the concatenation of the RLP encodings of the
//  items. The range of the first byte is thus [0xc0, 0xf7] (dec.
//  [192, 247]).
//
//  If the total payload of a list is more than 55 bytes long, the RLP
//  encoding consists of a single byte with value 0xf7 plus the length
//  in bytes of the length of the payload in binary form, followed by
//  the length of the payload, followed by the concatenation of the RLP
//  encodings of the items. The range of the first byte is thus
//  [0xf8, 0xff] (dec. [248, 255]).
namespace rlp
{

    namespace impl
    {
        // Rlp Types:
        //
        // Single byte whose value is in [0x00, 0x7f]
        //
        // Byte string between 0 and 55 bytes long
        constexpr inline uint8_t BYTES_55_BASE = 0x80;
        constexpr inline uint8_t BYTES_55_MIN = BYTES_55_BASE;

        // Byte string longer than 55 bytes
        constexpr inline uint8_t BYTES_GE_55_BASE = 0xb7;
        constexpr inline uint8_t BYTES_GE_55_MIN = BYTES_GE_55_BASE + 1;

        static_assert(BYTES_GE_55_BASE - BYTES_55_BASE == 55);

        // List where combined length of all RLP encoded items is
        // between 0 and 55 bytes long
        constexpr inline uint8_t LIST_55_BASE = 0xc0;
        constexpr inline uint8_t LIST_55_MIN = LIST_55_BASE;

        // List where combined length of all RLP encoded items is
        // greater than 55 bytes long
        constexpr inline uint8_t LIST_GE_55_BASE = 0xf7;
        constexpr inline uint8_t LIST_GE_55_MIN = LIST_55_BASE + 1;

        static_assert(LIST_GE_55_BASE - LIST_55_BASE == 55);

    }

    struct Encoding
    {
        byte_string bytes;

        constexpr bool operator==(Encoding const &) const = default;
    };

    namespace impl
    {
        template <class T>
        concept unsigned_integral =
            std::unsigned_integral<T> || std::same_as<uint256_t, T>;

        // size of bytes if leading zeroes were stripped off
        constexpr size_t size_of_compacted_num(unsigned_integral auto num)
        {
            auto const *start =
                reinterpret_cast<byte_string::value_type *>(&num);
            auto const *const end =
                reinterpret_cast<byte_string::value_type *>(&num + 1);

            while (start < end && *start == 0) {
                ++start;
            }
            return end - start;
        }

        // size of bytes required to represent num in big endian with leading
        // zeroes stripped off
        constexpr size_t
        size_of_big_endian_compacted_num(unsigned_integral auto num)
        {
            return size_of_compacted_num(intx::to_big_endian(num));
        }

        // convert integral type into big endian and compact into byte_string
        // array, stripping off leading zeroes
        constexpr byte_string
        to_big_endian_compacted(unsigned_integral auto num)
        {
            num = intx::to_big_endian(num);
            auto const compacted_size = size_of_compacted_num(num);
            auto const *const start =
                reinterpret_cast<byte_string::value_type *>(&num);

            return byte_string{
                start + sizeof(num) - compacted_size, compacted_size};
        }

        // Note - this type is not compacted, as it is stored as a string
        // instead of a number
        constexpr byte_string to_big_endian_compacted(bytes32_t bytes)
        {
            return byte_string{bytes.bytes, sizeof(bytes32_t)};
        }

        // Encode bytes into the target byte array
        constexpr void
        encode_single(byte_string &target, byte_string_view const &bytes)
        {
            // nothing in the header
            if (bytes.size() == 1 && bytes.front() < BYTES_55_MIN) {
                target.push_back(bytes.front());
                return;
            }

            if (bytes.size() <= 55) {
                target.push_back(BYTES_55_BASE + bytes.size());
            }
            else {
                auto const be_compacted_size =
                    to_big_endian_compacted(bytes.size());
                target.push_back(BYTES_GE_55_BASE + be_compacted_size.size());
                target += be_compacted_size;
            }

            target += bytes;
        }

        // encode header for an unsigned integral
        constexpr void
        encode_single(byte_string &target, unsigned_integral auto num)
        {
            if constexpr (sizeof(num) == 1) {
                if (num < BYTES_55_MIN) {
                    target.push_back(num);
                    return;
                }
            }

            auto const bytes = to_big_endian_compacted(num);
            encode_single(target, bytes);
        }

        inline void encode_single(byte_string &target, std::string const &str)
        {
            auto const *const ptr =
                reinterpret_cast<byte_string::value_type const *>(str.data());
            encode_single(target, byte_string_view{ptr, str.size()});
        }

        inline void encode_single(byte_string &target, bytes32_t const &bytes)
        {
            target.push_back(BYTES_55_BASE + sizeof(bytes32_t));
            target.append(bytes.bytes, sizeof(bytes32_t));
        }

        constexpr void
        encode_single(byte_string &target, Encoding const &encoding)
        {
            target += encoding.bytes;
        }

        // Returns the number of bytes needed to encode the bytes array
        constexpr size_t size_of_encoding(byte_string_view bytes)
        {
            if (bytes.size() == 1 && bytes.front() < BYTES_55_MIN) {
                // encoding is itself
                return 1;
            }

            // prefix byte concatenated with bytes
            auto const first_plus_payload = 1 + bytes.size();
            if (bytes.size() <= 55) {
                return first_plus_payload;
            }

            // for byte strings larger than 55, we also need to include
            // the number of bytes of the payload size
            return first_plus_payload +
                   size_of_big_endian_compacted_num(bytes.size());
        }

        inline size_t size_of_encoding(std::string const &str)
        {
            auto const *const ptr =
                reinterpret_cast<byte_string::value_type const *>(str.data());
            return size_of_encoding(byte_string_view{ptr, str.size()});
        }

        // Returns the number of bytes needed to encode the integral
        constexpr size_t size_of_encoding(unsigned_integral auto integral)
        {
            if (sizeof(integral) == 1 && integral < BYTES_55_MIN) {
                // encoding is itself
                return 1;
            }

            assert(sizeof(integral) <= 55);

            // defaults to prefix byte + number of bytes. for unsigned integral
            // types, this will always fall in the list-between-0-and-55 bytes
            // category
            return 1 + size_of_big_endian_compacted_num(integral);
        }

        constexpr size_t size_of_encoding(bytes32_t)
        {
            return 1 + sizeof(bytes32_t);
        }

        constexpr size_t size_of_encoding(Encoding const &encoding)
        {
            return encoding.bytes.size();
        }

    } // namespace impl

    // Supported types must define a `size_of_encoding` and `encode_single`
    // overload where the former returns the number of bytes of the encoded
    // object and the latter encodes the object.
    //
    // Support for encoding unsigned integral types, strings, byte_string, and
    // also supports nested Encoding.
    constexpr Encoding encode(auto const &...args)
    {
        constexpr auto is_empty_list = sizeof...(args) == 0;

        if constexpr (is_empty_list) {
            return Encoding{.bytes = byte_string(1, impl::LIST_55_BASE)};
        }

        constexpr auto is_non_empty_list = sizeof...(args) > 1;

        byte_string bytes;

        // Populate "header" bytes of list
        if constexpr (is_non_empty_list) {
            // get the encoding of all the lists members summed up
            auto const size = (impl::size_of_encoding(args) + ...);

            // this is the max representable size in RLP
            assert(size < std::numeric_limits<uint64_t>::max());

            if (size <= 55) {
                // header is just base + size
                bytes.reserve(size + 1);
                bytes.push_back(impl::LIST_55_BASE + size);
            }
            else {
                // header is (base + size of payload length, payload length)
                auto const be_compacted_size =
                    impl::to_big_endian_compacted(size);
                bytes.reserve(size + 1 + be_compacted_size.size());
                bytes.push_back(
                    impl::LIST_GE_55_BASE + be_compacted_size.size());
                bytes += be_compacted_size;
            }
        }

        // append all rlp payloads to the byte array
        (..., impl::encode_single(bytes, args));

        return Encoding{bytes};
    }

} // namespace rlp

MONAD_NAMESPACE_END
