#include "lightweight_binary_logger.h"

#include <atomic>
#include <chrono>
#include <condition_variable>
#include <csignal>
#include <cstddef>
#include <cstring>
#include <initializer_list>
#include <mutex>
#include <span>
#include <stop_token>
#include <string_view>
#include <thread>
#include <vector>

#include <fcntl.h>
#include <linux/mman.h>
#include <sys/mman.h>
#include <unistd.h>

#include <zstd.h>

#include <boost/container/devector.hpp>
#include <boost/outcome/experimental/status-code/status-code/posix_code.hpp>
#include <boost/outcome/experimental/status-code/status-code/system_code_from_exception.hpp>
#include <boost/outcome/experimental/status_result.hpp>
#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <monad/config.h>
#include <monad/core/assert.h>
#include <monad/core/async_signal_handling.hpp>
#include <monad/util/ticks_count.h>
#include <monad/util/ticks_count_impl.h>

namespace monad
{
    static constexpr size_t MONAD_LBL_MIN_LARGE_PAGES = 32;
    static constexpr size_t MONAD_LBL_HUGE_PAGE_SIZE = 2 * 1024 * 1024;

    template <class T>
    using result = boost::outcome_v2::experimental::status_result<T>;
    using boost::outcome_v2::success;
    using boost::outcome_v2::experimental::errc;
    using boost::outcome_v2::experimental::posix_code;

    struct monad_lbl_impl
    {
        monad_lbl_head head{};

        int fd{-1};
        monad_cpu_ticks_count_t last_entry_ticks{};
        std::jthread thread;
        std::vector<async_signal_handling::handler_ptr> signal_handlers;

        std::mutex lock;
        std::condition_variable new_towrite_cond, new_tofill_cond;
        boost::container::devector<std::span<std::byte>> tofill, towrite;
        std::span<std::byte> scratch;

        // WARNING: Runs in a different kernel thread!
        void worker_thread(std::stop_token tok)
        {
            std::unique_lock g(lock);
            while (!tok.stop_requested() || !towrite.empty()) {
                if (!towrite.empty()) {
                    auto const buff = towrite.front();
                    g.unlock();
                    auto written = ZSTD_compress(
                        scratch.data() + 4,
                        MONAD_LBL_HUGE_PAGE_SIZE - 4,
                        buff.data(),
                        buff.size(),
                        3 /* ultra fast */);
                    MONAD_ASSERT(!ZSTD_isError(written));
                    written += 4;
                    *(uint32_t *)scratch.data() = (uint32_t)written;
                    MONAD_ASSERT(
                        (ssize_t)written ==
                        ::write(fd, scratch.data(), written));
                    g.lock();
                    MONAD_ASSERT(buff.data() == towrite.front().data());
                    head.uncompressed_bytes_written += buff.size();
                    head.file_bytes_written += written;
                    towrite.pop_front();
                    tofill.emplace_back(buff.data(), 0);
                    new_tofill_cond.notify_one();
                }
                MONAD_ASSERT(refill_pages(&g));
                if (towrite.empty()) {
                    new_towrite_cond.wait(g);
                }
            }
        }

        result<void>
        refill_pages(std::unique_lock<std::mutex> *g, size_t max = (size_t)-1)
        {
            bool const first_run = (tofill.empty() && towrite.empty());
            size_t const tofillsize = first_run
                                          ? (MONAD_LBL_MIN_LARGE_PAGES << 1)
                                          : MONAD_LBL_MIN_LARGE_PAGES;
            while (tofill.size() < tofillsize && max > 0) {
                if (g != nullptr) {
                    g->unlock();
                }
                auto *const page = (std::byte *)mmap(
                    nullptr,
                    MONAD_LBL_HUGE_PAGE_SIZE,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB | MAP_HUGE_2MB |
                        MAP_POPULATE,
                    -1,
                    0);
                if (page == MAP_FAILED) {
                    return posix_code();
                }
                if (g != nullptr) {
                    g->lock();
                }
                tofill.emplace_back(page, 0);
                max--;
            }
            MONAD_ASSERT(!tofill.empty());
            return success();
        }

        result<void>
        append(std::initializer_list<std::span<std::byte const>> vec)
        {
            size_t total_length = 0;
            for (auto &i : vec) {
                total_length += i.size();
            }
            if (total_length > MONAD_LBL_HUGE_PAGE_SIZE) {
                return errc::argument_list_too_long;
            }
            if (total_length > 0) {
                std::unique_lock g(lock);
                while (towrite.size() > (MONAD_LBL_MIN_LARGE_PAGES << 2)) {
                    // The background writer can't keep up, have to stall
                    // foreground
                    new_tofill_cond.wait(g);
                    head.pacing_events++;
                }
                for (auto &i : vec) {
                    if (i.data() == nullptr || i.size() == 0) {
                        continue;
                    }
                    auto towritenow = std::min(
                        MONAD_LBL_HUGE_PAGE_SIZE - tofill.front().size(),
                        i.size());
                    {
                        auto &buff = tofill.front();
                        auto *const dest = buff.data() + buff.size();
                        memcpy(dest, i.data(), towritenow);
                        buff = {buff.data(), buff.size() + towritenow};
                        if (buff.size() == MONAD_LBL_HUGE_PAGE_SIZE) {
                            tofill.pop_front();
                            towrite.push_back(buff);
                            new_towrite_cond.notify_one();
                        }
                    }
                    if (i.size() != towritenow) {
                        auto const *const src = i.data() + towritenow;
                        towritenow = i.size() - towritenow;
                        if (tofill.empty()) {
                            // Must NOT drop locks mid-append
                            BOOST_OUTCOME_TRY(refill_pages(nullptr, 1));
                            head.write_buffer_starvation_events++;
                        }
                        auto &buff = tofill.front();
                        auto *const dest = buff.data() + buff.size();
                        memcpy(dest, src, towritenow);
                        buff = {buff.data(), buff.size() + towritenow};
                    }
                }
            }
            return success();
        }

        void install_signal_handlers()
        {
            static constexpr int signos[] = {SIGHUP, SIGINT, SIGTERM};
            static async_signal_handling inst;
            signal_handlers.reserve(sizeof(signos) / sizeof(signos[0]));
            for (auto const signo : signos) {
                signal_handlers.push_back(async_signal_handling::add_handler(
                    signo,
                    0,
                    [logger = this](
                        const struct signalfd_siginfo &,
                        async_signal_handling::handler *) -> bool {
                        (void)monad_lbl_flush((monad_lbl)logger);
                        return false;
                    }));
            }
        }
    };

    extern "C" monad_c_result monad_lbl_create(
        monad_lbl *logger, char const *path, void const *user_header,
        size_t user_header_bytes)
    {
        monad_lbl_impl *p;
        if (user_header_bytes + sizeof(monad_lbl_file_header) >
            MONAD_LBL_HUGE_PAGE_SIZE) {
            return monad_c_make_failure(E2BIG);
        }
        try {
            p = new (std::nothrow) monad_lbl_impl;
            if (p == nullptr) {
                return monad_c_make_failure(errno);
            }
            p->fd = ::open(
                path,
                O_WRONLY | O_APPEND | O_CLOEXEC | O_CREAT | O_TRUNC,
                0660);
            if (-1 == p->fd) {
                int const errcode = errno;
                delete p;
                return monad_c_make_failure(errcode);
            }
            std::string_view pv(path);
            if (pv.size() > 31) {
                pv = pv.substr(pv.size() - 31, 31);
            }
            memcpy(
                (char *)p->head.path,
                pv.data(),
                std::min(pv.size(), (size_t)31));
            ((char *)p->head.path)[31] = 0;
            p->scratch = {
                (std::byte *)mmap(
                    nullptr,
                    MONAD_LBL_HUGE_PAGE_SIZE,
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS | MAP_HUGETLB | MAP_HUGE_2MB |
                        MAP_POPULATE,
                    -1,
                    0),
                MONAD_LBL_HUGE_PAGE_SIZE};
            if (p->scratch.data() == MAP_FAILED) {
                posix_code().throw_exception();
            }
            p->refill_pages(nullptr).value();
            monad_lbl_file_header header{};
            memcpy(header.magic, "MNL0", 4);
            auto const now_ns = std::chrono::system_clock::now();
            p->last_entry_ticks = get_ticks_count(std::memory_order_seq_cst);
            header.utc_ns_count_on_creation =
                (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(
                    now_ns.time_since_epoch())
                    .count();
            header.cpu_ticks_on_creation = p->last_entry_ticks;
            header.user_supplied_header_bytes = (uint32_t)user_header_bytes;
            p->append({{(std::byte *)&header, sizeof(header)},
                       {(std::byte *)user_header, user_header_bytes}})
                .value();
            p->thread = std::jthread(
                [p](std::stop_token tok) { p->worker_thread(tok); });
            p->install_signal_handlers();
            *logger = (monad_lbl)p;
            return monad_c_make_success(0);
        }
        catch (...) {
            (void)monad_lbl_destroy(&p->head);
            return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                monad,
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>(BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                  system_code_from_exception()));
        }
    }

    extern "C" monad_c_result monad_lbl_destroy(monad_lbl logger)
    {
        try {
            monad_lbl_impl *p = (monad_lbl_impl *)logger;
            p->signal_handlers.clear();
            if (p->thread.joinable()) {
                monad_lbl_file_footer footer{};
                memcpy(footer.magic, "MNL0", 4);
                footer.uncompressed_content_length =
                    p->head.uncompressed_bytes_written;
                auto const now_ns = std::chrono::system_clock::now();
                footer.utc_ns_count_on_close =
                    (uint64_t)
                        std::chrono::duration_cast<std::chrono::nanoseconds>(
                            now_ns.time_since_epoch())
                            .count();
                footer.cpu_ticks_on_close =
                    get_ticks_count(std::memory_order_seq_cst);
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_lbl_add(
                    logger,
                    footer.magic,
                    sizeof(footer) - sizeof(struct monad_lbl_entry_header)));
                BOOST_OUTCOME_C_RESULT_SYSTEM_TRY(monad_lbl_flush(logger));
                {
                    std::lock_guard g(p->lock);
                    p->thread.request_stop();
                    p->new_towrite_cond.notify_one();
                }
                p->thread.join();
            }
            MONAD_ASSERT(p->towrite.empty());
            if (p->fd != -1) {
                ::close(p->fd);
                p->fd = -1;
            }
            if (p->scratch.data() != nullptr) {
                (void)::munmap(p->scratch.data(), MONAD_LBL_HUGE_PAGE_SIZE);
                p->scratch = {};
            }
            for (auto &i : p->tofill) {
                (void)::munmap(i.data(), MONAD_LBL_HUGE_PAGE_SIZE);
            }
            p->tofill.clear();
            delete p;
            return monad_c_make_success(0);
        }
        catch (...) {
            return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                monad,
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>(BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                  system_code_from_exception()));
        }
    }

    extern "C" monad_c_result
    monad_lbl_add(monad_lbl logger, void const *content, size_t bytes)
    {
        try {
            monad_lbl_impl *p = (monad_lbl_impl *)logger;
            monad_lbl_entry_header header{};
            if (bytes + sizeof(header) > (1u << 21u)) {
                return monad_c_make_failure(E2BIG);
            }
            header.length = ((bytes + sizeof(header)) & 0x1FFFFF);
            auto const now = get_ticks_count(std::memory_order_relaxed);
            header.cpu_ticks_delta =
                (now - p->last_entry_ticks) & 0x7FFFFFFFFFF;
            p->last_entry_ticks = now;
            p->append({{(std::byte *)&header, sizeof(header)},
                       {(std::byte *)content, bytes}})
                .value();
            return monad_c_make_success(0);
        }
        catch (...) {
            return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                monad,
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>(BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                  system_code_from_exception()));
        }
    }

    extern "C" monad_c_result monad_lbl_flush(monad_lbl logger)
    {
        try {
            monad_lbl_impl *p = (monad_lbl_impl *)logger;
            std::unique_lock g(p->lock);
            if (p->tofill.front().size() > 0) {
                auto page = p->tofill.front();
                p->tofill.pop_front();
                p->towrite.push_back(page);
                p->new_towrite_cond.notify_one();
            }
            p->new_tofill_cond.wait(g, [p] { return p->towrite.empty(); });
            return monad_c_make_success(0);
        }
        catch (...) {
            return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
                monad,
                BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<
                    intptr_t>(BOOST_OUTCOME_V2_NAMESPACE::experimental::
                                  system_code_from_exception()));
        }
    }

}
