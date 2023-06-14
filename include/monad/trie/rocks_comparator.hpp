#pragma once

#include <monad/core/address.hpp>

#include <monad/trie/comparator.hpp>
#include <monad/trie/config.hpp>

#include <rocksdb/comparator.h>
#include <rocksdb/slice.h>

#include <cassert>
#include <cstring>

MONAD_TRIE_NAMESPACE_BEGIN

// IMPORTANT: changes to the comparator are NOT backwards compatible with
// previous databases.
class PathComparator : public rocksdb::Comparator
{
public:
    virtual int
    Compare(rocksdb::Slice const &s1, rocksdb::Slice const &s2) const override
    {
        assert(!s1.empty());
        assert(!s2.empty());
        return path_compare(
            byte_string_view{
                reinterpret_cast<byte_string_view::value_type const *>(
                    s1.data()),
                s1.size()},
            byte_string_view{
                reinterpret_cast<byte_string_view::value_type const *>(
                    s2.data()),
                s2.size()});
    }

    // Update this whenever the logic of this compartor is changed
    virtual const char *Name() const override { return "PathComparator 0.0.1"; }

    void FindShortestSeparator(
        std::string *, rocksdb::Slice const &) const override final
    {
    }
    void FindShortSuccessor(std::string *) const override final {}
};

class PrefixPathComparator : public rocksdb::Comparator
{
    int Compare(
        rocksdb::Slice const &s1, rocksdb::Slice const &s2) const override final
    {
        assert(s1.size() > sizeof(address_t));
        assert(s2.size() > sizeof(address_t));

        auto const rc = std::memcmp(s1.data(), s2.data(), sizeof(address_t));
        if (rc != 0) {
            return rc;
        }

        auto bs1 = byte_string_view{
            reinterpret_cast<byte_string_view::value_type const *>(s1.data()),
            s1.size()};
        auto bs2 = byte_string_view{
            reinterpret_cast<byte_string_view::value_type const *>(s2.data()),
            s2.size()};
        bs1.remove_prefix(sizeof(address_t));
        bs2.remove_prefix(sizeof(address_t));

        return path_compare(bs1, bs2);
    }

    // Update this whenever the logic of this compartor is changed
    const char *Name() const override final
    {
        return "PrefixPathComparator 0.0.1";
    }

    // TODO: implement these for potential optimizations? Figure out what they
    // do
    void FindShortestSeparator(
        std::string *, rocksdb::Slice const &) const override final
    {
    }
    void FindShortSuccessor(std::string *) const override final {}
};

MONAD_TRIE_NAMESPACE_END
