#pragma once

#include "test_fixtures_base.hpp"

#include <monad/async/test/test_fixture.hpp>
#include <monad/mpt/db.hpp>
#include <monad/mpt/ondisk_db_config.hpp>
#include <monad/mpt/state_machine.hpp>

#include <memory>
#include <string_view>

namespace monad::test
{
    struct InMemoryMerkleTrieGTest
        : public MerkleTrie<InMemoryTrieBase<void, ::testing::Test>>
    {
        using MerkleTrie<
            InMemoryTrieBase<void, ::testing::Test>>::InMemoryTrieBase;
    };

    struct OnDiskMerkleTrieGTest
        : public MerkleTrie<OnDiskTrieBase<void, ::testing::Test>>
    {
        using MerkleTrie<OnDiskTrieBase<void, ::testing::Test>>::OnDiskTrieBase;
    };

    struct InMemoryTrieGTest
        : public PlainTrie<InMemoryTrieBase<void, ::testing::Test>>
    {
    };

    struct OnDiskTrieGTest
        : public PlainTrie<OnDiskTrieBase<void, ::testing::Test>>
    {
    };

    template <
        FillDBWithChunksConfig Config,
        monad::mpt::lockable_or_void LockType = void>
    struct FillDBWithChunksGTest
        : public FillDBWithChunks<Config, LockType, ::testing::Test>
    {
        using FillDBWithChunks<
            Config, LockType, ::testing::Test>::FillDBWithChunks;
    };

    class OnDiskDatabaseFixture : public ::testing::Test
    {
    protected:
        std::unique_ptr<mpt::Db> db_;
        std::filesystem::path dbname_;
        off_t size_;
        OnDiskDbConfig config_;

        OnDiskDatabaseFixture(off_t const size = 8ULL * 1024 * 1024 * 1024)
            : size_(size)
        {
        }

        virtual std::string_view fixture_template() = 0;
        virtual StateMachine &state_machine() = 0;

        mpt::Db &db()
        {
            return *db_;
        }

        void SetUp() override
        {
            dbname_ = MONAD_ASYNC_NAMESPACE::working_temporary_directory() /
                      fixture_template();
            int const fd = ::mkstemp((char *)dbname_.native().data());
            MONAD_ASSERT(fd != -1);
            MONAD_ASSERT(-1 != ::ftruncate(fd, size_));
            ::close(fd);

            db_ = std::make_unique<mpt::Db>(
                state_machine(),
                mpt::OnDiskDbConfig{
                    .append = false, .dbname_paths = {dbname_}});
        }

        void TearDown() override
        {
            std::filesystem::remove(dbname_);
        }

        virtual ~OnDiskDatabaseFixture() = default;
    };

}
