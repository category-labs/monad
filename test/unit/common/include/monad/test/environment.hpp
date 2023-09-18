#pragma once

#include <gtest/gtest.h>

#include <monad/core/assert.h>
#include <monad/test/config.hpp>

#include <quill/Quill.h>

MONAD_TEST_NAMESPACE_BEGIN

class Environment : public ::testing::Environment
{
public:
    void SetUp() override { quill::start(); }
};

MONAD_TEST_NAMESPACE_END
