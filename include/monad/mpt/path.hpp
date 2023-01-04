#pragma once

#include <algorithm>
#include <concepts>
#include <bits/iterator_concepts.h>
#include <cstdint>
#include <cstddef>

#include <fmt/core.h>

#include <monad/core/byte_string.hpp>
#include <monad/core/assert.h>
#include <monad/mpt/nibble.hpp>
#include <monad/config.hpp>

#include <range/v3/range/conversion.hpp>

MONAD_NAMESPACE_BEGIN

namespace mpt
{

// Use to specify if encoding a leaf or an extension node
struct EncodeLeaf {};
struct EncodeExtension {};

template <typename T>
concept EncodeMode = std::same_as<T, EncodeLeaf> or std::same_as<T, EncodeExtension>;

class Path;
class PathView;

namespace impl
{
template <typename DerivedPath>
struct BasicPathTraits;

template <>
struct BasicPathTraits<Path>
{
    using rep = Nibbles;
    using size_type = rep::size_type;
};

template <>
struct BasicPathTraits<PathView>
{
    using rep = NibblesView;
    using size_type = rep::size_type;
};

// Represents a path in the trie data structure. Each element in the
// path is a nibble.
template <typename PathType>
class BasicPath
{
public:
    using traits_type = BasicPathTraits<PathType>;
    using size_type = typename traits_type::size_type;

    constexpr BasicPath() = default;

    constexpr PathType& derived()
    {
        return *static_cast<PathType*>(this);
    }

    constexpr PathType const& derived() const
    {
        return *static_cast<PathType const*>(this);
    }

    // Number of *nibbles* in the path
    constexpr size_type size() const
    {
        return std::distance(derived().begin(), derived().end());
    }

    constexpr bool empty() const
    {
        return derived().begin() == derived().end();
    }

    // longest common prefix size
    constexpr size_type common_prefix_size(BasicPath const& path) const
    {
        auto const min = std::min(size(), path.size());
        for (size_type i = 0; i < min; ++i) {
            if (derived()[i] != static_cast<PathType const&>(path)[i]) {
                return i;
            }
        }
        return min;
    }

    // Transform the path to it's compact encoding
    // https://ethereum.org/en/developers/docs/data-structures-and-encoding/patricia-merkle-trie/
    template<EncodeMode Mode>
    constexpr byte_string compact_encoding() const
    {
        // Does not make sense to call this function if the path is empty
        // If this happens, then there's a bug in the code
        assert(not empty());

        auto it = derived().begin();

        byte_string bytes;

        // Populate first byte with the encoded path type and potentially
        // also the first nibble if number of nibbles is odd
        auto const first_byte = [&]() {
            auto const is_even = (size() % 2) == 0;
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
        MONAD_ASSERT((std::distance(it, derived().end()) % 2) == 0);

        // Should have an even number of nibbles to process now
        while (it != derived().end()) {
            // Combine both nibbles and then advance past them
            bytes.push_back((*it << 4) | *std::next(it));
            std::advance(it, 2);
        }

        return bytes;
    }

    constexpr bool operator==(BasicPath const&) const = default;

protected:
    static constexpr auto PREFIX_EXTENSION_EVEN = 0x00;
    static constexpr auto PREFIX_EXTENSION_ODD = 0x10;
    static constexpr auto PREFIX_LEAF_EVEN = 0x20;
    static constexpr auto PREFIX_LEAF_ODD = 0x30;
};

template <typename PathType>
class PathTemplate : public impl::BasicPath<PathType>
{
public:
    using traits_type = BasicPathTraits<PathType>;
    using rep = typename traits_type::rep;
    using size_type = typename traits_type::size_type;

protected:
    // TODO: change this to be a byte array rather than an
    // array of nibbles so that it's friendlier on the cache lines
    rep nibbles_;

public:
    constexpr PathTemplate() = default;

    template <typename InputIt>
    constexpr PathTemplate(InputIt first, InputIt last)
        : nibbles_(first, last)
    {
    }

    template <typename NibblesType>
        requires std::same_as<NibblesType, Nibbles> or
                 std::same_as<NibblesType, NibblesView>
    constexpr explicit PathTemplate(NibblesType const& nibbles)
        : nibbles_(nibbles)
    {
    }

    constexpr auto begin() noexcept
    {
        return nibbles_.begin();
    } 

    constexpr auto begin() const noexcept
    {
        return nibbles_.begin();
    } 

    constexpr auto end() noexcept
    {
        return nibbles_.end();
    }

    constexpr auto end() const noexcept
    {
        return nibbles_.end();
    }

    constexpr auto operator[](size_type pos) const
    {
        return nibbles_[pos];
    }

    byte_string underlying_bytes() const
    {
        return nibbles_ | ranges::to<byte_string>();
    }

    constexpr auto span() const
    {
        return std::span(nibbles_);
    }

    constexpr bool operator==(PathTemplate const& t) const
    {
        return std::ranges::equal(begin(), end(), t.begin(), t.end());
    }
};
} // namespace impl

// Non-owning version of Path
class PathView: public impl::PathTemplate<PathView>
{
public:
    using base = impl::PathTemplate<PathView>;
    using base::base;

    constexpr PathView(PathView const&) = default;

    constexpr PathView prefix(size_type n) const
    {
        assert(n <= size());
        return PathView(begin(), std::next(begin(), n));
    }

    constexpr PathView suffix(size_type n) const
    {
        assert(n <= size());
        return PathView(std::prev(end(), n), end());
    }

    constexpr PathView& operator=(PathView const&) = default;

    constexpr bool operator==(PathView const&) const = default;
};

class Path : public impl::PathTemplate<Path>
{
public:
    using base = impl::PathTemplate<Path>;
    using traits_type = impl::BasicPathTraits<Path>;

    using base::base;

    constexpr Path(PathView view)
        : Path(view.begin(), view.end())
    {
    }

    constexpr Path(Path const&) = default;

    constexpr explicit Path(std::initializer_list<Nibble> list)
        : impl::PathTemplate<Path>(Nibbles{list})
    {
    }


    struct FromRawBytes {};
    struct FromCompactEncoding {};

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

    operator PathView() const
    {
        return PathView(begin(), end());
    }

    constexpr Path& operator=(Path const&) = default;

private:
    // convert a byte view into nibbles
    constexpr void initialize_from_raw(byte_string_view raw)
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
