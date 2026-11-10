#include <quill/Quill.h>

#include <chrono>
#include <cstdlib>

#include <sched.h>

using namespace std::chrono_literals;

void f()
{
    auto last = std::chrono::steady_clock::now();
    while (true) {
        auto const now = std::chrono::steady_clock::now();
        auto const delta = std::chrono::duration_cast<std::chrono::nanoseconds>(now - last);
        if (delta > 100ns) {
            LOG_INFO("duration {}", delta);
        }
        last = now;
    }
}

int main()
{
    quill::Config const config{.backend_thread_cpu_affinity=2};
    quill::configure(config);
    quill::start();

    cpu_set_t set;
    CPU_ZERO(&set);
    CPU_SET(1, &set);

    if (sched_setaffinity(0, sizeof(set), &set)) {
        perror("set affinity");
        return EXIT_FAILURE;
    }

/*
    sched_param const param{.sched_priority = 1};
    int const result = sched_setscheduler(0, SCHED_FIFO, &param);
    if (result) {
        perror("set scheduler");
        return EXIT_FAILURE;
    }
*/

    f();

    return EXIT_SUCCESS;
}
