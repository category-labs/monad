#include <algorithm>
#include <bit>
#include <cerrno>
#include <charconv>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <format>
#include <memory>
#include <source_location>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>

#include <err.h>
#include <getopt.h>
#include <sysexits.h>

#include <monad/core/c_result.h>
#include <monad/core/likely.h>
#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_channel.h>
#include <monad/fiber/fiber_semaphore.h>
#include <monad/fiber/run_queue.h>

namespace fs = std::filesystem;
using std::chrono::duration_cast, std::chrono::seconds,
    std::chrono::nanoseconds;

constexpr intptr_t KIBI_MASK = (1L << 10) - 1;

static size_t g_fiber_stack_size = 1UL << 17; // 128 KiB
static auto g_benchmark_seconds = seconds{10};
static size_t g_run_queue_fibers = 256;

enum long_only_option
{
    LO_RUN_QUEUE_FIBERS
};

// clang-format off
static option longopts[] = {
    {.name = "list", .has_arg = 0, .flag = nullptr, .val = 'L'},
    {.name = "stack_shift", .has_arg = 1, .flag = nullptr, .val = 's'},
    {.name = "time", .has_arg = 1, .flag = nullptr, .val = 't'},
    {.name = "rq-fibers", .has_arg = 1, .flag = nullptr,
        .val = LO_RUN_QUEUE_FIBERS},
    {.name = "help", .has_arg = 1, .flag = nullptr, .val = 'h'},
    {}};
// clang-format on

extern char const *__progname;

static void usage(std::FILE *out)
{
    std::fprintf(
        out,
        "%s: [-Lh] [-t <sec>] [-s <shift>] [--rq-fibers <#>] [benchmark...]\n",
        __progname);
}

template <typename... Args>
[[noreturn]] static void bench_die(
    std::source_location const &srcloc, std::format_string<Args...> fmt,
    Args &&...args)
{
    // TODO(ken): should use <print> but we don't have it yet
    std::string s = std::format(
                        "FATAL at {}@{}:{}:{}: ",
                        srcloc.function_name(),
                        fs::path{srcloc.file_name()}.filename().string(),
                        srcloc.line(),
                        srcloc.column()) +
                    std::format(fmt, std::forward<Args>(args)...);
    if (errno == 0) {
        std::error_condition const ec{std::errc(errno)};
        s += std::format(
            ": {} ({}:{})", ec.message(), ec.category().name(), ec.value());
    }
    err(EX_SOFTWARE, "%s", s.c_str());
}

#define CHECK_Z(X)                                                             \
    do {                                                                       \
        if (MONAD_UNLIKELY((X) != 0)) {                                        \
            errno = (X);                                                       \
            bench_die(                                                         \
                std::source_location::current(),                               \
                "expected a zero return value from {}, got {}",                \
                #X,                                                            \
                (X));                                                          \
        }                                                                      \
    }                                                                          \
    while (0)

#define ASSERT_EQ(X, Y)                                                        \
    do {                                                                       \
        if (MONAD_UNLIKELY((X) != (Y))) {                                      \
            errno = 0;                                                         \
            bench_die(                                                         \
                std::source_location::current(),                               \
                "assert failed: {}",                                           \
                #X " == " #Y);                                                 \
        }                                                                      \
    }                                                                          \
    while (0)

struct benchmark;

static void switch_benchmark(benchmark const &);
static void run_queue_benchmark(benchmark const &);
static void channel_benchmark(benchmark const &);
static void semaphore_benchmark(benchmark const &);

static struct benchmark
{
    std::string_view name;
    std::string_view description;
    void (*func)(benchmark const &);
} g_bench_table[] = {
    {.name = "switch",
     .description = "performance of fiber context switch",
     .func = switch_benchmark},
    {.name = "rq",
     .description = "performance of run queue",
     .func = run_queue_benchmark},
    {.name = "chan",
     .description = "performance of fiber channels",
     .func = channel_benchmark},
    {.name = "sem",
     .description = "performance of fiber semaphores",
     .func = semaphore_benchmark}};

static int parse_options(int argc, char **argv)
{
    int ch;
    std::from_chars_result fcr;
    unsigned opt_uint;

    while ((ch = getopt_long(argc, argv, "s:t:Lh", longopts, nullptr)) != -1) {
        char const *const end_optarg =
            optarg ? optarg + std::strlen(optarg) : nullptr;

        switch (ch) {
        case 'L':
            for (benchmark &b : g_bench_table) {
                std::fprintf(
                    stdout, "%s:\t%s\n", data(b.name), data(b.description));
            }
            std::exit(0);

        case 's':
            fcr = std::from_chars(optarg, end_optarg, g_fiber_stack_size);
            if (fcr.ptr != end_optarg || std::to_underlying(fcr.ec) ||
                g_fiber_stack_size < 10 || g_fiber_stack_size > 30) {
                errx(EX_CONFIG, "bad -s|--stack-shift value '%s'", optarg);
            }
            break;

        case 't':
            fcr = std::from_chars(optarg, end_optarg, opt_uint);
            if (fcr.ptr != end_optarg || std::to_underlying(fcr.ec) ||
                opt_uint == 0 || opt_uint > 3000) {
                errx(EX_CONFIG, "bad -t|--time value '%s'", optarg);
            }
            g_benchmark_seconds = seconds{opt_uint};
            break;

        case LO_RUN_QUEUE_FIBERS:
            fcr = std::from_chars(optarg, end_optarg, g_run_queue_fibers);
            if (fcr.ptr != end_optarg || std::to_underlying(fcr.ec) ||
                g_run_queue_fibers < 1 || g_run_queue_fibers > 1U << 20) {
                errx(EX_CONFIG, "bad --rq-fibers value '%s'", optarg);
            }
            break;

        case 'h':
            usage(stdout);
            exit(0);

        case '?':
            [[fallthrough]];
        default:
            usage(stderr);
            std::exit(EX_USAGE);
        }
    }

    return optind;
}

static monad_c_result yield_forever(monad_fiber_args_t mfa)
{
    auto *const done = (std::atomic<bool> *)mfa.arg[0];
    intptr_t y = 0;
    while (!done->load(std::memory_order::relaxed)) {
        monad_fiber_yield(monad_c_make_success(y++));
    }
    return monad_c_make_success(y);
}

struct channel_test_data
{
    std::atomic<bool> done;
    monad_fiber_channel_t channel_a;
    monad_fiber_channel_t channel_b;
};

static monad_c_result channel_a_loop(monad_fiber_args_t mfa)
{
    channel_test_data *const test_data =
        std::bit_cast<channel_test_data *>(mfa.arg[0]);
    intptr_t count = 0;
    do {
        monad_fiber_msghdr_t *const msghdr = monad_fiber_channel_pop(
            &test_data->channel_a, MONAD_FIBER_PRIO_NO_CHANGE);
        ++count;
        monad_fiber_channel_push(&test_data->channel_b, msghdr);
    }
    while (!test_data->done.load(std::memory_order::acquire));
    return monad_c_make_success(count);
}

static monad_c_result channel_b_loop(monad_fiber_args_t mfa)
{
    channel_test_data *const test_data =
        std::bit_cast<channel_test_data *>(mfa.arg[0]);
    monad_fiber_msghdr_t msghdr, *m = &msghdr;
    intptr_t count = 0;
    monad_fiber_msghdr_init(
        &msghdr, {.iov_base = &count, .iov_len = sizeof count});
    m = &msghdr;
    do {
        monad_fiber_channel_push(&test_data->channel_a, m);
        ++count;
        m = monad_fiber_channel_pop(
            &test_data->channel_b, MONAD_FIBER_PRIO_NO_CHANGE);
    }
    while (!test_data->done.load(std::memory_order::acquire));
    return monad_c_make_success(count);
}

struct semaphore_test_data
{
    std::atomic<bool> done;
    monad_fiber_semaphore_t sem_a;
    monad_fiber_semaphore_t sem_b;
};

static monad_c_result sem_a_loop(monad_fiber_args_t mfa)
{
    semaphore_test_data *const test_data =
        std::bit_cast<semaphore_test_data *>(mfa.arg[0]);
    intptr_t count = 0;
    do {
        monad_fiber_semaphore_acquire(
            &test_data->sem_a, MONAD_FIBER_PRIO_NO_CHANGE);
        ++count;
        monad_fiber_semaphore_release(&test_data->sem_b, 1);
    }
    while (!test_data->done.load(std::memory_order::acquire));
    return monad_c_make_success(count);
}

static monad_c_result sem_b_loop(monad_fiber_args_t mfa)
{
    semaphore_test_data *const test_data =
        std::bit_cast<semaphore_test_data *>(mfa.arg[0]);
    intptr_t count = 0;
    do {
        monad_fiber_semaphore_release(&test_data->sem_a, 1);
        ++count;
        monad_fiber_semaphore_acquire(
            &test_data->sem_b, MONAD_FIBER_PRIO_NO_CHANGE);
    }
    while (!test_data->done.load(std::memory_order::acquire));
    return monad_c_make_success(count);
}

static void switch_benchmark(benchmark const &self)
{
    monad_fiber_t *fiber;
    monad_fiber_suspend_info_t suspend_info;
    std::atomic<bool> done{false};
    monad_fiber_attr_t fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};

    CHECK_Z(monad_fiber_create(&fiber_attr, &fiber));
    CHECK_Z(monad_fiber_set_function(
        fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        yield_forever,
        (monad_fiber_args_t){.arg = {(uintptr_t)&done}}));

    auto const start_time = std::chrono::system_clock::now();
    do {
        CHECK_Z(monad_fiber_run(fiber, &suspend_info));
        ASSERT_EQ(monad_result_has_value(suspend_info.eval), true);
        if ((suspend_info.eval.value & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            auto const now = std::chrono::system_clock::now();
            done.store(
                duration_cast<seconds>(now - start_time) >= g_benchmark_seconds,
                std::memory_order::release);
        }
    }
    while (!done);

    CHECK_Z(monad_fiber_run(fiber, &suspend_info));
    ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    monad_fiber_destroy(fiber);

    intptr_t const context_switch_count = suspend_info.eval.value + 1;
    double const nanos_per_switch =
        (double)(duration_cast<nanoseconds>(g_benchmark_seconds).count()) /
        (double)context_switch_count;
    std::fprintf(
        stdout,
        "%s:\tsingle core context switch rate: %lu sw/s, %.1f ns/sw\n",
        data(self.name),
        context_switch_count / g_benchmark_seconds.count(),
        nanos_per_switch);
}

void run_queue_benchmark(benchmark const &self)
{
    std::unique_ptr<monad_fiber_t *[]> fibers;
    monad_fiber_t *next_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_run_queue_t *rq;
    std::atomic<bool> done{false};
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};
    size_t run_count = 0;

    CHECK_Z(monad_run_queue_create(nullptr, g_run_queue_fibers, &rq));
    fibers = std::make_unique<monad_fiber_t *[]>(g_run_queue_fibers);
    for (size_t f = 0; f < g_run_queue_fibers; ++f) {
        CHECK_Z(monad_fiber_create(&fiber_attr, &fibers[f]));
        CHECK_Z(monad_fiber_set_function(
            fibers[f],
            MONAD_FIBER_PRIO_HIGHEST,
            yield_forever,
            (monad_fiber_args_t){.arg = {(uintptr_t)&done}}));
        CHECK_Z(monad_run_queue_try_push(rq, fibers[f]));
    }

    auto const start_time = std::chrono::system_clock::now();
    do {
        next_fiber = monad_run_queue_try_pop(rq);
        (void)monad_fiber_run(next_fiber, nullptr);
        if ((++run_count & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            auto const now = std::chrono::system_clock::now();
            done.store(
                duration_cast<seconds>(now - start_time) >= g_benchmark_seconds,
                std::memory_order::release);
        }
    }
    while (!done);

    while (!monad_run_queue_is_empty(rq)) {
        next_fiber = monad_run_queue_try_pop(rq);
        monad_fiber_run(next_fiber, &suspend_info);
        ASSERT_EQ(MF_SUSPEND_RETURN, suspend_info.suspend_type);
    }

    monad_run_queue_destroy(rq);
    for (size_t f = 0; f < g_run_queue_fibers; ++f) {
        monad_fiber_destroy(fibers[f]);
    }

    double const nanos_per_run_cycle =
        ((double)g_benchmark_seconds.count() * 1'000'000'000.0) /
        (double)run_count;
    fprintf(
        stdout,
        "%s:\tsingle core run cycle rate: %lu r/s, %.1f ns/r\n",
        data(self.name),
        run_count / static_cast<unsigned>(g_benchmark_seconds.count()),
        nanos_per_run_cycle);
}

static void channel_benchmark(benchmark const &self)
{
    monad_fiber_t *fibers[2];
    monad_fiber_t *next_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_run_queue_t *rq;
    channel_test_data test_data;
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};
    monad_fiber_ffunc_t *const fiber_funcs[] = {channel_a_loop, channel_b_loop};
    size_t run_count = 0;
    intptr_t wakeup_count = 0;

    test_data.done = false;
    monad_fiber_channel_init(&test_data.channel_a);
    monad_fiber_channel_init(&test_data.channel_b);
    CHECK_Z(monad_run_queue_create(nullptr, 2, &rq));
    for (int f = 0; f < 2; ++f) {
        monad_fiber_create(&fiber_attr, &fibers[f]);
        CHECK_Z(monad_fiber_set_function(
            fibers[f],
            MONAD_FIBER_PRIO_HIGHEST + f,
            fiber_funcs[f],
            {(uintptr_t)&test_data}));
        CHECK_Z(monad_run_queue_try_push(rq, fibers[f]));
    }

    auto const start_time = std::chrono::system_clock::now();
    do {
        next_fiber = monad_run_queue_try_pop(rq);
        (void)monad_fiber_run(next_fiber, nullptr);
        if ((++run_count & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            auto const now = std::chrono::system_clock::now();
            test_data.done.store(
                duration_cast<seconds>(now - start_time) >= g_benchmark_seconds,
                std::memory_order::release);
        }
    }
    while (!test_data.done);

    while (!monad_run_queue_is_empty(rq)) {
        next_fiber = monad_run_queue_try_pop(rq);
        monad_fiber_run(next_fiber, &suspend_info);
        if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
            wakeup_count += suspend_info.eval.value;
            monad_fiber_destroy(next_fiber);
        }
    }

    monad_run_queue_destroy(rq);

    double const nanos_per_wakeup =
        ((double)g_benchmark_seconds.count() * 1'000'000'000.0) / (double)wakeup_count;
    std::fprintf(
        stdout,
        "%s:\tsingle core channel wakeup rate: %lu w/s, %.1f ns/w\n",
        data(self.name),
        wakeup_count / static_cast<unsigned>(g_benchmark_seconds.count()),
        nanos_per_wakeup);
}

static void semaphore_benchmark(benchmark const &self)
{
    monad_fiber_t *fibers[2];
    monad_fiber_t *next_fiber;
    monad_fiber_suspend_info_t suspend_info;
    monad_run_queue_t *rq;
    semaphore_test_data test_data;
    monad_fiber_attr_t const fiber_attr = {
        .stack_size = g_fiber_stack_size, .alloc = nullptr};
    monad_fiber_ffunc_t *const fiber_funcs[] = {sem_a_loop, sem_b_loop};
    size_t run_count = 0;
    intptr_t wakeup_count = 0;

    test_data.done = false;
    monad_fiber_semaphore_init(&test_data.sem_a);
    monad_fiber_semaphore_init(&test_data.sem_b);
    CHECK_Z(monad_run_queue_create(nullptr, 2, &rq));
    for (int f = 0; f < 2; ++f) {
        monad_fiber_create(&fiber_attr, &fibers[f]);
        CHECK_Z(monad_fiber_set_function(
            fibers[f],
            MONAD_FIBER_PRIO_HIGHEST + f,
            fiber_funcs[f],
            {(uintptr_t)&test_data}));
        CHECK_Z(monad_run_queue_try_push(rq, fibers[f]));
    }

    auto const start_time = std::chrono::system_clock::now();
    do {
        next_fiber = monad_run_queue_try_pop(rq);
        (void)monad_fiber_run(next_fiber, nullptr);
        if ((++run_count & KIBI_MASK) == 0) {
            // Every 1024 yields, check if it's time to exit
            auto const now = std::chrono::system_clock::now();
            test_data.done.store(
                duration_cast<seconds>(now - start_time) >= g_benchmark_seconds,
                std::memory_order::release);
        }
    }
    while (!test_data.done);

    while (!monad_run_queue_is_empty(rq)) {
        next_fiber = monad_run_queue_try_pop(rq);
        monad_fiber_run(next_fiber, &suspend_info);
        if (suspend_info.suspend_type == MF_SUSPEND_RETURN) {
            wakeup_count += suspend_info.eval.value;
            monad_fiber_destroy(next_fiber);
        }
    }

    monad_run_queue_destroy(rq);

    double const nanos_per_wakeup =
        ((double)g_benchmark_seconds.count() * 1'000'000'000.0) / (double)wakeup_count;
    std::fprintf(
        stdout,
        "%s:\tsingle core semaphore wakeup rate: %lu w/s, %.1f ns/w\n",
        data(self.name),
        wakeup_count / static_cast<unsigned>(g_benchmark_seconds.count()),
        nanos_per_wakeup);
}

int main(int argc, char **argv)
{
    char const *pos_arg;
    int next_pos_arg_idx = parse_options(argc, argv);

    if (next_pos_arg_idx == argc) {
        // Not specifying any benchmark runs all of them
        for (benchmark &b : g_bench_table) {
            b.func(b);
            std::fflush(stdout);
        }
    }
    while (next_pos_arg_idx != argc) {
        // If there are position arguments, run the benchmark named by the
        // argument; run with -L to see a list
        pos_arg = argv[next_pos_arg_idx++];
        auto const i_bench =
            std::ranges::find(g_bench_table, pos_arg, &benchmark::name);
        if (i_bench != std::end(g_bench_table)) {
            i_bench->func(*i_bench);
            std::fflush(stdout);
        }
        else {
            warnx("benchmark %s not found", pos_arg);
        }
    }

    return 0;
}
