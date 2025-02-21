#pragma GCC diagnostic ignored "-Wunused-function"

#include <monad/context/config.h>

#include "monad/async/util.h"

#include "executor_impl.h"
#include "task_impl.h"

#include <cerrno>
#include <chrono>
#include <cstring>
#include <filesystem>
#include <sstream>

#include <fcntl.h> // for open
#include <sys/vfs.h> // for statfs
#include <unistd.h> // for unlink

#include <boost/outcome/experimental/status-code/status-code/system_code_from_exception.hpp>

static std::filesystem::path const &working_temporary_directory()
{
    static std::filesystem::path const v = [] {
        std::filesystem::path ret;
        auto test_path = [&](std::filesystem::path const path) -> bool {
            int fd = ::open(path.c_str(), O_RDWR | O_DIRECT | O_TMPFILE, 0600);
            if (-1 == fd && ENOTSUP == errno) {
                auto path2 = path / "monad_XXXXXX";
                fd = mkostemp(
                    const_cast<char *>(path2.native().c_str()), O_DIRECT);
                if (-1 != fd) {
                    unlink(path2.c_str());
                }
            }
            if (-1 != fd) {
                struct statfs s = {};
                if (-1 == fstatfs(fd, &s)) {
                    ::close(fd);
                    return false;
                }
                ::close(fd);
                if (s.f_type == 0x01021994 /* tmpfs */) {
                    return false;
                }
                ret = path;
                return true;
            }
            return false;
        };
        // Only observe environment variables if not a SUID or SGID situation
        // FIXME? Is this actually enough? What about the non-standard saved
        // uid/gid? Should I be checking if my executable is SUGID and its
        // owning user is not mine?
        if (getuid() == geteuid() && getgid() == getegid()) {
            // Note that XDG_RUNTIME_DIR is the systemd runtime directory for
            // the current user, usually mounted with tmpfs XDG_CACHE_HOME  is
            // the systemd cache directory for the current user, usually at
            // $HOME/.cache
            static char const *variables[] = {
                "TMPDIR",
                "TMP",
                "TEMP",
                "TEMPDIR",
                "XDG_RUNTIME_DIR",
                "XDG_CACHE_HOME"};
            for (auto const *variable : variables) {
                char const *env = getenv(variable);
                if (env != nullptr) {
                    if (test_path(env)) {
                        return ret;
                    }
                }
            }
            // Also try $HOME/.cache
            char const *env = getenv("HOME");
            if (env != nullptr) {
                std::filesystem::path buffer(env);
                buffer /= ".cache";
                if (test_path(buffer)) {
                    return ret;
                }
            }
        }
        // TODO: Use getpwent_r() to extract current effective user home
        // directory Hardcoded fallbacks in case environment is not available to
        // us
        if (test_path("/tmp")) {
            return ret;
        }
        if (test_path("/var/tmp")) {
            return ret;
        }
        if (test_path("/run/user/" + std::to_string(geteuid()))) {
            return ret;
        }
        // Some systems with no writable hardcode fallbacks may have shared
        // memory configured
        if (test_path("/run/shm")) {
            return ret;
        }
        // On some Docker images this is the only writable path anywhere
        if (test_path("/")) {
            return ret;
        }
        throw std::runtime_error(
            "This system appears to have no writable temporary files location, "
            "please set one using any of the usual environment variables e.g. "
            "TMPDIR");
    }();
    return v;
}

extern "C" char const *monad_async_working_temporary_directory()
{
    return working_temporary_directory().c_str();
}

extern "C" int monad_async_make_temporary_file(char *buffer, size_t buffer_len)
{
    auto scratch = working_temporary_directory() / "monad_XXXXXX";
    if (scratch.native().size() > buffer_len - 1) {
        errno = ENOSPC;
        return -1;
    }
    memcpy(buffer, scratch.c_str(), scratch.native().size() + 1);
    return mkstemp(buffer);
}

extern "C" int monad_async_make_temporary_inode()
{
    int fd =
        ::open(working_temporary_directory().c_str(), O_RDWR | O_TMPFILE, 0600);
    if (-1 == fd && ENOTSUP == errno) {
        // O_TMPFILE is not supported on ancient Linux kernels
        // of the kind apparently Github like to run :(
        auto buffer = working_temporary_directory() / "monad_XXXXXX";
        fd = mkstemp(const_cast<char *>(buffer.native().c_str()));
        if (-1 != fd) {
            unlink(buffer.c_str());
        }
    }
    if (fd == -1) {
        fprintf(
            stderr,
            "FATAL: Failed to make temporary inode due to '%s'\n",
            strerror(errno));
        abort();
    }
    return fd;
}

extern "C" enum monad_async_memory_accounting_kind
monad_async_memory_accounting()
{
    static enum monad_async_memory_accounting_kind v {
        monad_async_memory_accounting_kind_unknown
    };

    if (v != monad_async_memory_accounting_kind_unknown) {
        return v;
    }
    int const fd = ::open("/proc/sys/vm/overcommit_memory", O_RDONLY);
    if (fd != -1) {
        char buffer[8];
        if (::read(fd, buffer, 8) > 0) {
            if (buffer[0] == '2') {
                v = monad_async_memory_accounting_kind_commit_charge;
            }
            else {
                v = monad_async_memory_accounting_kind_over_commit;
            }
        }
        ::close(fd);
    }
    return v;
}

extern "C" monad_context_cpu_ticks_count_t
monad_async_get_ticks_count(std::memory_order rel)
{
    return get_ticks_count(rel);
}

extern "C" monad_context_cpu_ticks_count_t monad_async_ticks_per_second()
{
    static monad_context_cpu_ticks_count_t v;
    if (v != 0) {
        return v;
    }
    std::array<double, 10> results;
    for (auto &result : results) {
        auto count1a = get_ticks_count(std::memory_order_acq_rel);
        auto ts1 = std::chrono::high_resolution_clock::now();
        auto count1b = get_ticks_count(std::memory_order_acq_rel);
        while (std::chrono::high_resolution_clock::now() - ts1 <
               std::chrono::milliseconds(100)) {
        }
        auto count2a = get_ticks_count(std::memory_order_acq_rel);
        auto ts2 = std::chrono::high_resolution_clock::now();
        auto count2b = get_ticks_count(std::memory_order_acq_rel);
        result = (double)(count2a + count2b - count1a - count1b) / 2.0 /
                 ((double)std::chrono::duration_cast<std::chrono::nanoseconds>(
                      ts2 - ts1)
                      .count() /
                  1000000000.0);
    }
    std::sort(results.begin(), results.end());
    v = (monad_context_cpu_ticks_count_t)((results[4] + results[5]) / 2);
    return v;
}

extern "C" monad_c_result
monad_async_executor_config_string(monad_async_executor ex_)
{
    try {
        struct monad_async_executor_impl *ex =
            (struct monad_async_executor_impl *)ex_;
        std::stringstream ss;
        auto write_ring_config = [&ss, &ex](io_uring *ring) {
            if (ring->ring_fd != 0) {
                ss << "io_uring header v" << IO_URING_VERSION_MAJOR << "."
                   << IO_URING_VERSION_MINOR << " library v"
                   << io_uring_major_version() << "."
                   << io_uring_minor_version();
                ss << "\nring fd " << ring->ring_fd << " has "
                   << ring->sq.ring_entries << " sq entries and "
                   << ring->cq.ring_entries << " cq entries.\nFeatures:";
                for (size_t n = 0; n < 32; n++) {
                    if (ring->features & (1u << n)) {
                        switch (n) {
                        case 0:
                            ss << " single_mmap";
                            break;
                        case 1:
                            ss << " nodrop";
                            break;
                        case 2:
                            ss << " submit_stable";
                            break;
                        case 3:
                            ss << " rw_cur_pos";
                            break;
                        case 4:
                            ss << " cur_personality";
                            break;
                        case 5:
                            ss << " fast_poll";
                            break;
                        case 6:
                            ss << " poll_32bits";
                            break;
                        case 7:
                            ss << " sqpoll_nonfixed";
                            break;
                        case 8:
                            ss << " ext_arg";
                            break;
                        case 9:
                            ss << " native_workers";
                            break;
                        case 10:
                            ss << " rsrc_tags";
                            break;
                        case 11:
                            ss << " cqe_skip";
                            break;
                        case 12:
                            ss << " linked_file";
                            break;
                        case 13:
                            ss << " reg_reg_ring";
                            break;
                        default:
                            ss << " unknown_bit_" << n;
                            break;
                        }
                    }
                }
                ss << "\nSetup:";
                for (size_t n = 0; n < 32; n++) {
                    if (ring->flags & (1u << n)) {
                        switch (n) {
                        case 0:
                            ss << " iopoll";
                            break;
                        case 1:
                            ss << " sqpoll";
                            break;
                        case 2:
                            ss << " sq_aff";
                            break;
                        case 3:
                            ss << " cqsize";
                            break;
                        case 4:
                            ss << " clamp";
                            break;
                        case 5:
                            ss << " attach_wq";
                            break;
                        case 6:
                            ss << " r_disabled";
                            break;
                        case 7:
                            ss << " submit_all";
                            break;
                        case 8:
                            ss << " coop_taskrun";
                            break;
                        case 9:
                            ss << " taskrun_flag";
                            break;
                        case 10:
                            ss << " sqe128";
                            break;
                        case 11:
                            ss << " cqe32";
                            break;
                        case 12:
                            ss << " single_issuer";
                            break;
                        case 13:
                            ss << " defer_taskrun";
                            break;
                        case 14:
                            ss << " no_mmap";
                            break;
                        case 15:
                            ss << " registered_fd_only";
                            break;
                        default:
                            ss << " unknown_bit_" << n;
                            break;
                        }
                    }
                }
                ss << "\nThere are "
                   << ex->registered_buffers[0].buffer[0].count
                   << " small registered non-write buffers of "
                   << ex->registered_buffers[0].buffer[0].size
                   << " bytes of which "
                   << ex->registered_buffers[0].buffer[0].buf_ring_count
                   << " are kernel allocated.";
                ss << "\nThere are "
                   << ex->registered_buffers[0].buffer[1].count
                   << " large registered non-write buffers of "
                   << ex->registered_buffers[0].buffer[1].size
                   << " bytes of which "
                   << ex->registered_buffers[0].buffer[1].buf_ring_count
                   << " are kernel allocated.";
                ss << "\nThere are "
                   << ex->registered_buffers[1].buffer[0].count
                   << " small registered write buffers of "
                   << ex->registered_buffers[1].buffer[0].size << " bytes";
                ss << "\nThere are "
                   << ex->registered_buffers[1].buffer[1].count
                   << " large registered write buffers of "
                   << ex->registered_buffers[1].buffer[1].size << " bytes";
                ss << "\n";
            }
        };
        write_ring_config(&ex->ring);
        write_ring_config(&ex->wr_ring);
        void *mem = malloc(ss.str().size() + 1);
        if (mem == nullptr) {
            return monad_c_make_failure(errno);
        }
        memcpy(mem, ss.str().data(), ss.str().size() + 1);
        return monad_c_make_success((intptr_t)mem);
    }
    catch (...) {
        return BOOST_OUTCOME_C_TO_RESULT_SYSTEM_CODE(
            monad,
            BOOST_OUTCOME_V2_NAMESPACE::experimental::status_result<intptr_t>(
                BOOST_OUTCOME_V2_NAMESPACE::experimental::
                    system_code_from_exception()));
    }
}
