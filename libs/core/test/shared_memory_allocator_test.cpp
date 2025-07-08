#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/mem/shared_memory_allocator.hpp>

#include <gtest/gtest.h>

#include <fcntl.h>
#include <random>
#include <sys/mman.h>

MONAD_NAMESPACE_BEGIN

#define NPROCS 10
#define SHMNAME "/my_shared_memory"
#define SHMSIZE 1 << 30
#define SHMADDR static_cast<char *>(reinterpret_cast<void *>(0x111000000000))
#define NUMITEMS 10
#define BENCHITERATIONS 10'000'000UL
#define STRESSITERATIONS 100'000UL

unsigned my_rand(unsigned tid)
{
    static thread_local std::mt19937 generator(tid);
    std::uniform_int_distribution<unsigned> distribution(0, 1 << 30);
    return distribution(generator);
}

struct Item
{
    SpinLock lock_;
    void *ptr_{nullptr};
    size_t size_{0};
    char pad_[104];
};

// Microbenchmark

void bench(
    unsigned const id, SharedMemoryAllocator &a, uint64_t const iterations)
{
    (void)id;
    for (uint64_t i = iterations; i; --i) {
        size_t const sz = 8;
        void *const ptr = a.alloc(sz);
        a.dealloc(ptr, sz);
    }
}

// Stress test

void stress(
    unsigned const id, SharedMemoryAllocator &a, uint64_t const iterations,
    Item *const items)
{
    (void)id;
    for (uint64_t i = 0; i < iterations; ++i) {
        unsigned const r = my_rand(id);
        unsigned const exp = 3 + r % 20;
        size_t const sz1 = (1 << exp) + r % (1 << exp);
        void *const ptr1 = a.alloc(sz1);
        unsigned const ind = r % NUMITEMS;
        auto &item = items[ind];
        void *ptr2;
        size_t sz2;
        {
            std::unique_lock g(item.lock_);
            ptr2 = std::exchange(item.ptr_, ptr1);
            sz2 = std::exchange(item.size_, sz1);
        }
        if (ptr2) {
            a.dealloc(ptr2, sz2);
        }
    }
}

// Create, run, and wait for children

template <class Func>
void run_processes(unsigned const nprocs, Func const fn)
{
    std::vector<pid_t> children;
    for (unsigned id = 0; id < nprocs; ++id) {
        pid_t pid = fork();
        if (pid == 0) {
            fn(id);
            exit(0);
        }
        else if (pid < 0) {
            perror("fork");
        }
        else {
            MONAD_DEBUG_ASSERT(pid > 0);
            children.emplace_back(pid);
        }
    }
    for (auto const &pid : children) {
        int status;
        waitpid(pid, &status, 0);
    }
}

template <class Func>
void run_threads(unsigned const nthreads, Func const fn)
{
    std::vector<std::thread> thr;
    for (unsigned tid = 0; tid < nthreads; ++tid) {
        thr.emplace_back([&, tid] { fn(tid); });
    }
    for (auto &t : thr) {
        t.join();
    }
}

// Shared memory setup and cleanup

void *call_mmap(int const fd)
{
    return mmap(
        SHMADDR,
        SHMSIZE,
        PROT_READ | PROT_WRITE,
        MAP_SHARED | MAP_FIXED,
        fd,
        0);
}

void *set_up_shared_memory()
{
    int const fd = shm_open(SHMNAME, O_CREAT | O_RDWR, 0666);
    if (ftruncate(fd, SHMSIZE)) {
        perror("ftruncate");
    }
    void *const ptr = call_mmap(fd);
    MONAD_DEBUG_ASSERT(ptr);
    SharedMemoryAllocator a(SHMSIZE, ptr, true);
    return ptr;
}

void clean_up_shared_memory(void *const ptr, size_t const size)
{
    munmap(ptr, size);
    shm_unlink(SHMNAME);
}

// Microbenchmarks

void run_bench_procs()
{
    void *const ptr = set_up_shared_memory();
    unsigned const nprocs = NPROCS;
    run_processes(nprocs, [](unsigned const id) {
        int const fd = shm_open(SHMNAME, O_RDWR, 0666);
        void *const ptr = call_mmap(fd);
        {
            SharedMemoryAllocator a(SHMSIZE, ptr, false);
            bench(id, a, BENCHITERATIONS);
        }
        munmap(ptr, SHMSIZE);
    });
    clean_up_shared_memory(ptr, SHMSIZE);
}

void run_bench_threads()
{
    void *const ptr = set_up_shared_memory();
    unsigned const nthreads = NPROCS;
    run_threads(nthreads, [ptr](unsigned const id) {
        SharedMemoryAllocator a(SHMSIZE, ptr, false);
        bench(id, a, BENCHITERATIONS);
    });
}

// Stress tests

Item *set_up_items(void *const ptr)
{
    SharedMemoryAllocator a(SHMSIZE, ptr, false);
    Item *const items = static_cast<Item *>(a.alloc(NUMITEMS * sizeof(Item)));
    std::memset(static_cast<void *>(items), 0, NUMITEMS * sizeof(Item));
    return items;
}

void clean_up_items(void *const ptr, Item *const items)
{
    SharedMemoryAllocator a(SHMSIZE, ptr, false);
    for (unsigned i = 0; i < NUMITEMS; ++i) {
        if (items[i].ptr_) {
            a.dealloc(items[i].ptr_, items[i].size_);
        }
    }
    std::memset(static_cast<void *>(items), 0xbbu, NUMITEMS * sizeof(Item));
    a.dealloc(items, NUMITEMS * sizeof(Item));
}

void run_stress_procs()
{
    void *const ptr = set_up_shared_memory();
    Item *const items = set_up_items(ptr);
    unsigned const nprocs = NPROCS;
    run_processes(nprocs, [items](unsigned const id) {
        int const fd = shm_open(SHMNAME, O_RDWR, 0666);
        void *const ptr = call_mmap(fd);
        {
            SharedMemoryAllocator a(SHMSIZE, ptr, false);
            stress(id, a, STRESSITERATIONS, items);
        }
        munmap(ptr, SHMSIZE);
    });
    clean_up_items(ptr, items);
    clean_up_shared_memory(ptr, SHMSIZE);
}

void run_stress_threads()
{
    void *const ptr = set_up_shared_memory();
    Item *const items = set_up_items(ptr);
    unsigned const nthreads = NPROCS;
    run_threads(nthreads, [ptr, items](unsigned const id) {
        SharedMemoryAllocator a(SHMSIZE, ptr, false);
        stress(id, a, STRESSITERATIONS, items);
    });
    clean_up_items(ptr, items);
}

// PROCESSES

TEST(shared_memory_allocator, bench_procs)
{
    run_bench_procs();
}

TEST(shared_memory_allocator, stress_procs)
{
    run_stress_procs();
}

// THREADS
TEST(shared_memory_allocator, bench_threads)
{
    quill::start();
    run_bench_threads();
}

TEST(shared_memory_allocator, stress_threads)
{
    quill::start();
    run_stress_threads();
}

MONAD_NAMESPACE_END
