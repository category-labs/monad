#include <monad/mem/dynamic_allocator.hpp>

#include <monad/test/gtest_signal_stacktrace_printer.hpp>  // NOLINT

#include <gtest/gtest.h>

#include <sys/mman.h>

#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>

// The fixture for testing class DynamicAllocator.
class AllocatorTest : public ::testing::TestWithParam<size_t>
{
    void SetUp() override
    {
        b = mmap(
            nullptr,
            (1 << size_bit),
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0);
        allocator = new (b) monad::DynamicAllocator<8, 11, 4, 13>(
            (char *)(b) + sizeof(monad::DynamicAllocator<8, 11, 4, 132>),
            (1 << size_bit) - sizeof(monad::DynamicAllocator<8, 11, 4, 13>));
    }
    void TearDown() override
    {
        munmap(b, 1 << size_bit);
    }

protected:
    void *b;
    int size_bit = 19;
    monad::DynamicAllocator<8, 11, 4, 13> *allocator;
};

/**
 * Tests the case when multiple pages within a superpage are created.
 */
TEST_P(AllocatorTest, TestOneSlot)
{
    constexpr int N = 250;
    size_t const size = GetParam();
    void *pointers[N];
    for (int i = 0; i < N; i++) // will go over two page sizes
    {
        pointers[i] = allocator->alloc(size);
        memset((char *)pointers[i], (i % 10) - '0', size - 1);
        memset(&((char *)pointers[i])[size - 1], '\0', 1);
        EXPECT_NE(pointers[i], nullptr);
    }
    for (int i = 0; i < N; i++) {
        char *temp = (char *)malloc(size);
        memset(temp, (i % 10) - '0', size - 1);
        memset(&temp[size - 1], '\0', 1);
        EXPECT_EQ(strcmp((char *)pointers[i], temp), 0);
        allocator->dealloc(pointers[i]);
        free(temp);
    }
}

TEST_P(AllocatorTest, FullAllocation)
{
    // allocate till run out of space
    uintptr_t ptr;
    size_t k = 0;
    size_t const size = GetParam();
    while ((ptr = (uintptr_t)(allocator->alloc(size))) != (uintptr_t) nullptr) {
        k++;
    }
    size_t const total_size =
        (1 << size_bit) - sizeof(monad::DynamicAllocator<8, 11, 4, 13>);
    size_t const page_size = 1 << 13;
    size_t const n_pages = (total_size) / page_size;
    size_t const n_blocks = (page_size - 48) / ((size - 1) / 16 * 16 + 16);
    EXPECT_EQ(n_pages * n_blocks, k);
}

INSTANTIATE_TEST_SUITE_P(
    DifferentSizes, AllocatorTest, ::testing::Values(500, 603, 700, 900, 1100));

/**
 * Test the case when blocks of different sizes are allocated.
 */
TEST_F(AllocatorTest, DifferentSizes)
{
    // large size shouldn't be allowed
    EXPECT_EQ(allocator->alloc(5000), nullptr);

    for (size_t t = 50; t <= 500; t++) {
        void *ptr = allocator->alloc(t);
        EXPECT_NE(ptr, nullptr);
    }
}
