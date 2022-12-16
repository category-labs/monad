#pragma once

#include <concepts>
#include <monad/core/byte_string.hpp>
#include <monad/core/assert.h>
#include <monad/mpt/nibble.hpp>
#include <cstdint>
#include <cstddef>
#include <monad/config.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

// Use to specify if encoding a leaf or an extension node
struct EncodeLeaf {};
struct EncodeExtension {};

template <typename T>
concept EncodeMode = std::same_as<T, EncodeLeaf> or std::same_as<T, EncodeExtension>;

// Represents a path in the trie data structure. Each element in the
// path is a nibble.
class Path
{
private:
    static constexpr auto PREFIX_EXTENSION_EVEN = 0x00;
    static constexpr auto PREFIX_EXTENSION_ODD = 0x10;
    static constexpr auto PREFIX_LEAF_EVEN = 0x20;
    static constexpr auto PREFIX_LEAF_ODD = 0x30;

    Nibbles nibbles_;

public:
    using size_type = Nibbles::size_type;
    using iterator = Nibbles::iterator; 
    using const_iterator = Nibbles::const_iterator;

    struct FromRawBytes {};
    struct FromCompactEncoding {};

    template <typename InputIt>
    constexpr Path(InputIt first, InputIt last)
        : nibbles_(first, last)
    {
    }

    constexpr explicit Path(Nibbles const& nibbles) 
        : nibbles_(nibbles)
    {
    }

    // NB: By using this constructor, one acknowledges that only even
    // numbers of nibbles can be represented due to the fact that
    // the trailing nibble would not be accurately represented. This
    // is in part what the compact encoding scheme aims to solve.
    //
    // Please consider using either the nibbles or the compact encoding
    // constructor if this is a concern.
    constexpr Path(byte_string_view raw, FromRawBytes)
    {
        initialize_from_raw(raw);
    } 

    // Construct a Path from a compact encoding
    constexpr Path(byte_string_view bytes, FromCompactEncoding)
    {
        // Does not make sense for compact encoding to be empty
        assert(not bytes.empty());

        auto const first_byte = bytes.front();

        // Note: Path does not care if extension or leaf node 
        switch (first_byte & 0xf0) {
            case PREFIX_EXTENSION_EVEN:
            case PREFIX_LEAF_EVEN:
                // Second nibble should be 0x0
                assert((first_byte & 0x0f) == 0);
                break;
            case PREFIX_EXTENSION_ODD:
            case PREFIX_LEAF_ODD:
                nibbles_.push_back(Nibble{
                    static_cast<unsigned char>(first_byte & 0x0f)
                });
                break;
            default:
                assert(false);
        }

        // remove the first byte and process the rest as if they were
        // raw
        bytes.remove_prefix(1);
        initialize_from_raw(bytes);
    }

    constexpr auto begin() noexcept -> iterator { return nibbles_.begin(); } 
    constexpr auto cbegin() const noexcept -> const_iterator { return nibbles_.cbegin(); } 
    constexpr auto end() noexcept -> iterator { return nibbles_.end(); }
    constexpr auto cend() const noexcept -> const_iterator { return nibbles_.cend(); }

    // Number of *nibbles* in the path
    constexpr auto size() const -> size_type
    {
        return nibbles_.size();
    }

    constexpr auto empty() const -> bool
    {
        return nibbles_.empty();
    }

    // trim to the first n characters
    constexpr auto trim_to_prefix(size_type n) -> void
    {
        assert(n <= size());

        nibbles_.resize(n);
    }

    // Remove n characters from the beginning of the path
    constexpr auto remove_prefix(size_type n) -> void
    {
        assert(n <= size());

        nibbles_.erase(nibbles_.begin(), std::next(nibbles_.begin(), n));
    }

    // longest common prefix size
    constexpr auto common_prefix_size(Path const& path) const -> size_type
    {
        auto const min = std::min(size(), path.size());
        for (size_type i = 0; i < min; ++i) {
            if (nibbles_[i] != path[i]) {
                return i;
            }
        }
        return min;
    }

    // Transform the path to it's compact encoding
    // https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
    template<EncodeMode Mode>
    constexpr auto compact_encoding() const -> byte_string
    {
        // Does not make sense to call this function if the path is empty
        // If this happens, then there's a bug in the code
        assert(not empty());

        auto it = nibbles_.begin();

        byte_string bytes;

        // Populate first byte with the encoded path type and potentially
        // also the first nibble if number of nibbles is odd
        auto const first_byte = [&]() {
            auto const is_even = (nibbles_.size() % 2) == 0;
            if constexpr (std::same_as<Mode, EncodeLeaf>) {
                if (is_even) {
                    return PREFIX_LEAF_EVEN;
                } else {
                    auto const first_byte = PREFIX_LEAF_ODD | *it;
                    std::advance(it, 1);
                    return first_byte;
                }
            } else {
                if (is_even) {
                    return PREFIX_EXTENSION_EVEN;
                } else {
                    auto const first_byte = PREFIX_EXTENSION_ODD | *it;
                    std::advance(it, 1);
                    return first_byte;
                }
            }
        }();

        bytes.push_back(first_byte);

        // should be an even number of hops away from the end
        MONAD_ASSERT((std::distance(it, nibbles_.end()) % 2) == 0);

        // Should have an even number of nibbles to process now
        while (it != nibbles_.end()) {
            // Combine both nibbles and then advance past them
            bytes.push_back((*it << 4) | *std::next(it));
            std::advance(it, 2);
        }

        return bytes;
    }

    constexpr bool operator==(Path const&) const = default;

    constexpr bool operator==(Nibbles const& nibbles) const
    {
        return nibbles_ == nibbles;
    }

    constexpr Nibble operator[](Nibbles::size_type index) const
    {
        assert(index < nibbles_.size());
        return nibbles_[index];
    }

private:
    // convert a byte view into nibbles
    constexpr auto initialize_from_raw(byte_string_view raw) -> void
    {
        constexpr auto RIGHT_NIBBLE = 0x0f;

        for (auto const byte : raw) {
            nibbles_.push_back(Nibble{static_cast<unsigned char>(byte >> 4)});
            nibbles_.push_back(Nibble{static_cast<unsigned char>(byte & RIGHT_NIBBLE)});
        }
    }
};
}  // namespace mpt

MONAD_NAMESPACE_END
