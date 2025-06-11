#pragma once

#include <monad/async/util.hpp>
#include <monad/core/assert.h>
#include <monad/core/cleanup.h>
#include <monad/test/config.hpp>

#include <gtest/gtest.h>

#include <deque>
#include <filesystem>
#include <format>
#include <stdlib.h>

MONAD_TEST_NAMESPACE_BEGIN

struct ResourceOwningFixture : public ::testing::Test
{
    std::deque<std::filesystem::path> files;
    std::string format{std::format(
        "monad_test_{}_XXXXXX",
        ::testing::UnitTest::GetInstance()->current_test_info()->name())};

    std::filesystem::path create_temp_file(off_t const size)
    {
        std::filesystem::path filename{
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() / format};
        int fd [[gnu::cleanup(cleanup_close)]] =
            ::mkstemp((char *)filename.native().data());
        MONAD_ASSERT(fd != -1);
        MONAD_ASSERT(-1 != ::ftruncate(fd, size));
        files.emplace_back(filename);
        return filename;
    }

    std::filesystem::path create_temp_dir()
    {
        std::filesystem::path root{
            MONAD_ASYNC_NAMESPACE::working_temporary_directory() / format};
        MONAD_ASSERT(mkdtemp((char *)root.native().data()));
        files.emplace_back(root);
        return root;
    }

    virtual void TearDown() override
    {
        for (auto const &path : files) {
            MONAD_ASSERT(std::filesystem::remove_all(path));
        }
    }
};

MONAD_TEST_NAMESPACE_END
