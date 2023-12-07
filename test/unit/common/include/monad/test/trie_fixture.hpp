#pragma once

#include <monad/test/make_db.hpp>
#include <monad/test/one_hundred_updates.hpp>
#include <monad/trie/comparator.hpp>
#include <monad/trie/in_memory_cursor.hpp>
#include <monad/trie/in_memory_writer.hpp>
#include <monad/trie/trie.hpp>

#include <quill/bundled/fmt/chrono.h>
#include <quill/bundled/fmt/format.h>

#include <gtest/gtest.h>

#include <filesystem>

namespace fmt = fmtquill::v10;

MONAD_TEST_NAMESPACE_BEGIN

template <typename TComparator>
struct in_memory_fixture : public ::testing::Test
{
    using cursor_t = monad::trie::InMemoryCursor<TComparator>;
    using writer_t = monad::trie::InMemoryWriter<TComparator>;
    using trie_t = monad::trie::Trie<cursor_t, writer_t>;
    using storage_t = std::map<byte_string, byte_string, TComparator>;

    storage_t leaves_storage_;
    storage_t trie_storage_;
    cursor_t leaves_cursor_;
    cursor_t trie_cursor_;
    writer_t leaves_writer_;
    writer_t trie_writer_;
    trie_t trie_;

    in_memory_fixture()
        : leaves_cursor_(leaves_storage_)
        , trie_cursor_(trie_storage_)
        , leaves_writer_(leaves_storage_)
        , trie_writer_(trie_storage_)
        , trie_(leaves_cursor_, trie_cursor_, leaves_writer_, trie_writer_)
    {
    }

    void flush()
    {
        leaves_writer_.write();
        trie_writer_.write();
    }

    void process_updates(std::vector<monad::trie::Update> const &updates)
    {
        trie_.process_updates(updates);
        flush();
    }

    void clear()
    {
        trie_.clear();
        flush();
    }

    bool storage_empty() const
    {
        return leaves_storage_.empty() && trie_storage_.empty();
    }
};

[[nodiscard]] constexpr monad::trie::Update
make_upsert(monad::trie::Nibbles const &key, byte_string const &value)
{
    return monad::trie::Upsert{
        .key = key,
        .value = value,
    };
}

[[nodiscard]] constexpr monad::trie::Update
make_upsert(bytes32_t key, byte_string const &value)
{
    return make_upsert(monad::trie::Nibbles(key), value);
}

[[nodiscard]] inline monad::trie::Update
make_upsert(bytes32_t const &key, bytes32_t const &value)
{
    return make_upsert(
        monad::trie::Nibbles(key),
        byte_string(
            reinterpret_cast<byte_string::value_type const *>(&value.bytes),
            sizeof(value.bytes)));
}

[[nodiscard]] constexpr monad::trie::Update
make_del(monad::trie::Nibbles const &key)
{
    return monad::trie::Delete{
        .key = key,
    };
}

[[nodiscard]] constexpr monad::trie::Update make_del(evmc::bytes32 key)
{
    return make_del(monad::trie::Nibbles(key));
}

[[nodiscard]] constexpr std::vector<monad::trie::Update>
make_updates(std::ranges::range auto const &updates)
{
    std::vector<monad::trie::Update> ret;
    for (auto const &[key, value] : updates) {
        ret.emplace_back(make_upsert(key, value));
    }
    return ret;
}

MONAD_TEST_NAMESPACE_END
