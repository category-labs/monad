#pragma once

#include <gtest/gtest.h>

#include <monad/core/assert.h>
#include <monad/logging/monad_log.hpp>
#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

class Environment : public ::testing::Environment
{
public:
    void SetUp() override
    {
        monad::log::logger_t::start();

        (void)monad::log::logger_t::create_logger("trie_db_logger");
        (void)monad::log::logger_t::create_logger("rocks_db_logger");

        monad::log::logger_t::set_log_level(
            "trie_db_logger", monad::log::level_t::Info);
        monad::log::logger_t::set_log_level(
            "rocks_db_logger", monad::log::level_t::Info);
    }
};

MONAD_TEST_NAMESPACE_END
