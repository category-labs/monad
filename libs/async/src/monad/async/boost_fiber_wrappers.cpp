#include <monad/async/boost_fiber_wrappers.hpp>

#include <monad/async/config.hpp>
#include <monad/async/erased_connected_operation.hpp>
#include <boost/fiber/buffered_channel.hpp>
#include <boost/fiber/channel_op_status.hpp>
#include <boost/fiber/condition_variable.hpp>
#include <boost/fiber/context.hpp>
#include <boost/fiber/fiber.hpp>
#include <boost/fiber/mutex.hpp>

#include <mutex>

MONAD_ASYNC_NAMESPACE_BEGIN

namespace boost_fibers::detail
{
    extern void detach_fiber_from_current_thread_and_initiate(
        detached_thread_context &context, ::boost::fibers::context *todetach,
        erased_connected_operation *initiate)
    {
        // We need a helper fibre one running per kernel thread
        struct msg_t
        {
            ::boost::fibers::mutex *mtx;
            ::boost::fibers::condition_variable *cond;
            ::boost::fibers::context *context;
            erased_connected_operation *initiate;
        };
        static thread_local struct helper_fiber_t
        {
            ::boost::fibers::buffered_channel<msg_t> channel{2};
            ::boost::fibers::fiber fiber;

            helper_fiber_t()
                : fiber(&helper_fiber_t::run, this)
            {
            }
            ~helper_fiber_t()
            {
                channel.close();
                fiber.join();
            }
            void run()
            {
                msg_t msg;
                while (::boost::fibers::channel_op_status::success ==
                       channel.pop(msg)) {
                    std::unique_lock const g(*msg.mtx);
                    msg.context->detach();
                    // Initiate the thread transfer
                    msg.initiate->initiate();
                }
            }
        } helper_fiber;
        ::boost::fibers::mutex mtx;
        ::boost::fibers::condition_variable cond;
        context.cond = &cond;
        context.context = todetach;
        std::unique_lock g(mtx);
        helper_fiber.channel.push(msg_t{
            .mtx = &mtx,
            .cond = &cond,
            .context = todetach,
            .initiate = initiate});
        /* From inspecting the source code, a condvar
        sleep is safe to combine with context detach and reattach
        */
        cond.wait(g);
    }

    extern void attach_fiber_to_current_thread_and_resume(
        ::boost::fibers::context *onto, const detached_thread_context &context)
    {
        onto->attach(context.context);
        context.cond->notify_all();
    }

}

MONAD_ASYNC_NAMESPACE_END
