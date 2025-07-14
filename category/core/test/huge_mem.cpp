#include <category/core/mem/huge_mem.hpp>

#include <category/core/config.hpp>
#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp>  // NOLINT

#include <gtest/gtest.h>

#include <iostream>

TEST(HugeMem, works)
{
    using namespace MONAD_NAMESPACE;
    HugeMem const mem(5);
    std::cerr << "HugeMem construction was successful" << std::endl;
    unsigned char volatile *p = mem.get_data();
    p[0] = 5;
    std::cerr << "HugeMem write was successful" << std::endl;
}
