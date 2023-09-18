#pragma once

#include <gtest/gtest.h>

#include <monad/core/assert.h>
#include <monad/test/config.hpp>

#include <quill/Quill.h>

MONAD_TEST_NAMESPACE_BEGIN

class Environment : public ::testing::Environment
{
public:
    void SetUp() override
    {
        quill::start();

        auto *trie_db_logger = quill::create_logger("trie_db_logger");
        auto *rocks_db_logger = quill::create_logger("rocks_db_logger");
        auto *block_logger = quill::create_logger("block_logger");
        auto *evmone_baseline_interpreter_logger =
            quill::create_logger("evmone_baseline_interpreter_logger");
        auto *state_logger = quill::create_logger("state_logger");
        auto *change_set_logger = quill::create_logger("change_set_logger");
        auto *txn_logger = quill::create_logger("txn_logger");

        MONAD_DEBUG_ASSERT(trie_db_logger);
        MONAD_DEBUG_ASSERT(rocks_db_logger);
        MONAD_DEBUG_ASSERT(block_logger);
        MONAD_DEBUG_ASSERT(evmone_baseline_interpreter_logger);
        MONAD_DEBUG_ASSERT(state_logger);
        MONAD_DEBUG_ASSERT(change_set_logger);
        MONAD_DEBUG_ASSERT(txn_logger);
    }
};

MONAD_TEST_NAMESPACE_END
