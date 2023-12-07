#pragma once

#include <monad/core/assert.h>
#include <monad/db/in_memory_trie_db.hpp>
#include <monad/test/config.hpp>
#include <test_resource_data.h>

#include <algorithm>
#include <chrono>
#include <filesystem>

#include <quill/bundled/fmt/chrono.h>
#include <quill/bundled/fmt/format.h>

#include <gtest/gtest.h>

namespace fmt = fmtquill::v10;

MONAD_TEST_NAMESPACE_BEGIN

template <typename TDatabase>
inline TDatabase make_db()
{
    auto const *info = testing::UnitTest::GetInstance()->current_test_info();
    MONAD_ASSERT(info);

    return TDatabase{};
}

MONAD_TEST_NAMESPACE_END
