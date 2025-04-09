#include <monad/fiber2/dispatcher.hpp>
//#include <monad/fiber2/future.hpp>
//#include <monad/fiber2/scheduler.hpp>

#include <boost/context/fiber.hpp>

#include <quill/Quill.h>

#include <condition_variable>
#include <cstdlib>
#include <deque>
#include <iostream>
#include <mutex>
#include <thread>
#include <utility>

#include <unistd.h>

using namespace monad;

/*
static std::deque<boost::context::fiber> ready_queue{};

void scheduler_loop()
{
    while (true) {
        if (ready_queue.size()) {
            boost::context::fiber fiber{std::move(ready_queue.front())};
            ready_queue.pop_front();
            fiber = std::move(fiber).resume();
            if (fiber) {
                ready_queue.emplace_back(std::move(fiber));
            }
        }
    }
}

template <typename Fn>
void start(Fn &&fn)
{
    ready_queue.emplace_back(
        [fn = std::move(fn)](boost::context::fiber &&fiber) {
            fiber::dispatcher_ = std::move(fiber);
            fn();
            return std::move(fiber::dispatcher_);
        });
}

struct Future
{
    bool set_{false};
    boost::context::fiber fiber_{};

    void release()
    {
        set_ = true;
        if (fiber_) {
            ready_queue.emplace_back(std::move(fiber_));
        }
    }

    void wait()
    {
        if (!set_) {
            fiber::dispatcher_ =
                std::move(fiber::dispatcher_)
                    .resume_with([this](boost::context::fiber &&fiber) {
                        fiber_ = std::move(fiber);
                        return boost::context::fiber{};
                    });
        }
    }
};
*/

/*
void start()
{
    ready_queue.emplace_back([](boost::context::fiber &&fiber) {
        scheduler = std::move(fiber);
        std::cout << "first" << std::endl;
        fiber::yield();
        std::cout << "second" << std::endl;
        fiber::yield();
        std::cout << "third" << std::endl;
        return std::move(scheduler);
    });
}
*/

fiber::Future futures[4] = {{}, {}, {}, {}};

void f(int const i)
{
    std::cout << i << " first" << std::endl;
    // fiber::yield();
    futures[i].wait();
    std::cout << i << " second" << std::endl;
    if (i >= 1) {
        futures[i - 1].set_value();
    }
    fiber::yield();
    std::cout << i << " third" << std::endl;
}

void f1(int const fiber_num)
{
    for (unsigned i = 0; i < 5; ++i) {
        LOG_INFO("fiber={} result={}", fiber_num, i);
        fiber::yield();
    }
    //LOG_INFO("{} first", i);
    //std::cout << i << " first" << std::endl;
    //fiber::yield();
    //LOG_INFO("{} second", i);
    //std::cout << i << " second" << std::endl;
    //fiber::yield();
    //LOG_INFO("{} third", i);
    //std::cout << i << " third" << std::endl;
}

int main1()
{
    futures[3].set_value();
    for (int i = 0; i < 4; ++i) {
        fiber::start([i] { f(i); });
        //fiber::start(i, [i] { f(i); });
        // start();
    }

    /*
    while (true) {
        fiber::dispatch();
    }
    */

    std::stop_token stop_token;
    fiber::run(stop_token);

    return 0;
}

int main2()
{
    for (int i = 0; i < 3; ++i) {
        //fiber::start(i, [i] { f1(i); });
        fiber::start([i] { f1(i); });
    }

    /*
    while (true) {
        fiber::dispatch();
    }
    */

    std::stop_token stop_token;
    fiber::run(stop_token);

    return 0;
}

int main()
{
    quill::start();

    LOG_INFO("main");

    std::vector<std::thread> threads{};

    std::stop_source stop_source;

    for (unsigned i = 0; i < 4; ++i) {
        std::thread thread{[i, stop_token = stop_source.get_token()] {
            LOG_INFO("thread {}", i);
            //std::cout << "thread " << i << std::endl;
            fiber::run(stop_token);
            //sleep(std::rand() % 15);
        }};
        threads.emplace_back(std::move(thread));
    }

    sleep(1);

    for (int i = 0; i < 3; ++i) {
        //fiber::start(i, [i] { f1(i); });
        fiber::start([i] { f1(i); });
    }

    sleep(15);

    stop_source.request_stop();

    for (auto& thread: threads) {
        thread.join();
    }

    return 0;
}
