#pragma once

#include <monad/core/assert.h>
#include <monad/db/util.hpp>
#include <monad/trie/key_buffer.hpp>
#include <monad/trie/nibbles.hpp>
#include <monad/trie/util.hpp>

#include <rocksdb/db.h>
#include <rocksdb/options.h>

#include <tl/optional.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

struct RocksCursor
{
    std::shared_ptr<rocksdb::DB> const db_;

    byte_string lower_;
    byte_string upper_;
    rocksdb::Slice lower_slice_;
    rocksdb::Slice upper_slice_;
    std::unique_ptr<rocksdb::Iterator> it_;
    rocksdb::ColumnFamilyHandle *cf_; // non-owning
    rocksdb::ReadOptions read_opts_;
    mutable KeyBuffer buf_;

    struct Key
    {
        bool has_prefix;
        byte_string raw;

        [[nodiscard]] constexpr bool operator==(Key const &) const = default;

        [[nodiscard]] constexpr Nibbles path() const
        {
            MONAD_DEBUG_ASSERT(!has_prefix || raw.size() > sizeof(address_t));
            return deserialize_nibbles(
                       has_prefix ? raw.substr(sizeof(address_t)) : raw)
                .first;
        }

        [[nodiscard]] constexpr bool path_empty() const
        {
            MONAD_DEBUG_ASSERT(!has_prefix || raw.size() > sizeof(address_t));
            return (has_prefix ? raw[sizeof(address_t)] : raw[0]) == 0;
        }
    };

    RocksCursor(
        std::shared_ptr<rocksdb::DB> db, rocksdb::ColumnFamilyHandle *cf)
        : db_(db)
        , cf_(cf)
    {
        MONAD_DEBUG_ASSERT(cf);
    }

    [[nodiscard]] tl::optional<RocksCursor::Key> key() const
    {
        return valid() ? tl::make_optional(Key{
                             .has_prefix = (buf_.prefix_size > 0),
                             .raw = byte_string{db::from_slice(it_->key())}})
                       : tl::nullopt;
    }

    [[nodiscard]] tl::optional<byte_string> value() const
    {
        return valid() ? tl::make_optional(
                             byte_string{db::from_slice(it_->value())})
                       : tl::nullopt;
    }

    void prev()
    {
        if (it_->Valid()) {
            it_->Prev();
        }
        else {
            // Note: weird quirk here where we just seek to last if the
            // iterator is not valid. This means that if we prev() from
            // the very first node, and then prev() again, that will bring
            // us to the very last element in the database. This is why we
            // valid() to avoid running into this by accident
            it_->SeekToLast();
            MONAD_ASSERT(valid());
        }

        MONAD_ASSERT(it_->Valid() || it_->status().ok());
    }

    void next()
    {
        if (it_->Valid()) {
            it_->Next();
        }
        else {
            // Note: similar quirky behavior to prev()
            it_->SeekToFirst();
            MONAD_ASSERT(valid());
        }

        MONAD_ASSERT(it_->Valid() || it_->status().ok());
    }

    void lower_bound(
        Nibbles const &key, tl::optional<Key> const &first = tl::nullopt,
        tl::optional<Key> const &last = tl::nullopt)
    {
        bool new_iterator = !it_;

        // set up the read options
        if (first) {
            if (read_opts_.iterate_lower_bound == nullptr ||
                *read_opts_.iterate_lower_bound != db::to_slice(first->raw)) {
                new_iterator = true;
                lower_ = first->raw;
                lower_slice_ =
                    rocksdb::Slice{(const char *)lower_.data(), lower_.size()};
                read_opts_.iterate_lower_bound = &lower_slice_;
            }
        }
        else if (read_opts_.iterate_lower_bound != nullptr) {
            new_iterator = true;
            read_opts_.iterate_lower_bound = nullptr;
        }

        if (last) {
            if (read_opts_.iterate_upper_bound == nullptr ||
                *read_opts_.iterate_upper_bound != db::to_slice(last->raw)) {
                new_iterator = true;
                upper_ = last->raw;
                upper_slice_ =
                    rocksdb::Slice{(const char *)upper_.data(), upper_.size()};
                read_opts_.iterate_upper_bound = &upper_slice_;
            }
        }
        else if (read_opts_.iterate_upper_bound != nullptr) {
            new_iterator = true;
            read_opts_.iterate_upper_bound = nullptr;
        }

        // only create the new iterator if needed
        if (new_iterator) {
            it_.reset(db_->NewIterator(read_opts_, cf_));
        }

        serialize_nibbles(buf_, key);
        it_->Seek(db::to_slice(buf_.view()));
        MONAD_ASSERT(it_->Valid() || it_->status().ok());
    }

    [[nodiscard]] bool valid() const
    {
        return it_ && it_->Valid() &&
               it_->key().starts_with(db::to_slice(buf_.prefix()));
    }

    [[nodiscard]] bool empty()
    {
        lower_bound({});
        return !valid();
    }

    constexpr void set_prefix(address_t const &address) noexcept
    {
        buf_.set_prefix(address);
    }

    void reset() noexcept { it_.reset(); };
};

[[nodiscard]] inline Nibbles deserialize_nibbles(rocksdb::Slice slice)
{
    auto const [nibbles, size] = deserialize_nibbles(
        {(byte_string_view::value_type *)slice.data(), slice.size()});
    MONAD_ASSERT(size == slice.size());
    return nibbles;
}

MONAD_TRIE_NAMESPACE_END
