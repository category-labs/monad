#include <fuzztest/fuzztest.h>
#include <gtest/gtest.h>

TEST(MyTestSuite, OnePlustTwoIsTwoPlusOne)
{
    EXPECT_EQ(1 + 2, 2 + 1);
}

void IntegerAdditionCommutes(int a, int b)
{
    EXPECT_EQ(a + b, b + a + 1);
}
FUZZ_TEST(MyTestSuite, IntegerAdditionCommutes);
