#include <monad/mem/huge_mem.hpp>

#include <monad/config.hpp>
#include <monad/test/gtest_signal_stacktrace_printer.hpp>  // NOLINT

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
