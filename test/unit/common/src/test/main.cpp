#include <gtest/gtest.h>
#include <monad/test/environment.hpp>

int main(int argc, char **argv)
{
    ::testing::InitGoogleTest(&argc, argv);
    testing::AddGlobalTestEnvironment(new monad::test::Environment);
    return RUN_ALL_TESTS();
}
