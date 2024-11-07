#pragma GCC diagnostic ignored "-Wunused-function"

#include "executor.h"

#include "executor_impl.h"

#include <sstream>

#include <boost/outcome/experimental/status-code/status-code/system_code_from_exception.hpp>

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
