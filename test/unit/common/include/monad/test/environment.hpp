#pragma once

#include <gtest/gtest.h>

#include <monad/logging/monad_log.hpp>
#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

class Environment : public ::testing::Environment
{
public:
    void SetUp() override
    {
        monad::log::logger_t::start();

        auto *logger = monad::log::logger_t::create_logger("trie_db_logger");
        MONAD_ASSERT(logger);

        monad::log::logger_t::set_log_level(
            "trie_db_logger", monad::log::level_t::Info);
    }
};

MONAD_TEST_NAMESPACE_END
