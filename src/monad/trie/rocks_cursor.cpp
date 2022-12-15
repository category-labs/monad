#include <monad/trie/rocks_cursor.hpp>
#include <tl/optional.hpp>

MONAD_TRIE_NAMESPACE_BEGIN

RocksCursor::RocksCursor(
    std::shared_ptr<rocksdb::DB> db, rocksdb::ColumnFamilyHandle *cf)
    : db_(db)
    , cf_(cf)
{
    read_opts_.snapshot = db_->GetSnapshot();

    assert(cf);
    assert(read_opts_.snapshot);
}

tl::optional<RocksCursor::Key> RocksCursor::key() const
{
    return valid() ? tl::make_optional(
                         Key{.has_prefix = (buf_.prefix_size > 0),
                             .raw = byte_string{from_slice(it_->key())}})
                   : tl::nullopt;
}

tl::optional<byte_string> RocksCursor::value() const
{
    return valid() ? tl::make_optional(byte_string{from_slice(it_->value())})
                   : tl::nullopt;
}

void RocksCursor::prev()
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

void RocksCursor::next()
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

bool RocksCursor::valid() const
{
    return it_ && it_->Valid() &&
           it_->key().starts_with(to_slice(buf_.prefix()));
}

void RocksCursor::lower_bound(
    Nibbles const &key, tl::optional<Key> const &first,
    tl::optional<Key> const &last)
{
    assert(read_opts_.snapshot);

    bool new_iterator = !it_;

    // set up the read options
    if (first) {
        if (read_opts_.iterate_lower_bound == nullptr ||
            *read_opts_.iterate_lower_bound != to_slice(first->raw)) {
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
            *read_opts_.iterate_upper_bound != to_slice(last->raw)) {
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
    it_->Seek(to_slice(buf_.view()));
    MONAD_ASSERT(it_->Valid() || it_->status().ok());
}

bool RocksCursor::empty()
{
    lower_bound({});
    return !valid();
}

void RocksCursor::take_snapshot()
{
    release_snapshots();
    assert(!it_);
    read_opts_.snapshot = db_->GetSnapshot();
}

void RocksCursor::release_snapshots()
{
    assert(read_opts_.snapshot);
    db_->ReleaseSnapshot(read_opts_.snapshot);
    it_.reset();
}

void RocksCursor::set_prefix(address_t const &address)
{
    buf_.set_prefix(address);
}

Nibbles deserialize_nibbles(rocksdb::Slice slice)
{
    auto [nibbles, size] = deserialize_nibbles(
        {(byte_string_view::value_type *)slice.data(), slice.size()});
    MONAD_ASSERT(size == slice.size());
    return std::move(nibbles);
}

MONAD_TRIE_NAMESPACE_END
