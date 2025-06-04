#include <monad/config.hpp>
#include <monad/core/block.hpp>
#include <monad/fiber/priority_pool.hpp>

#include <boost/fiber/future/promise.hpp>

MONAD_NAMESPACE_BEGIN

std::vector<std::optional<Address>>
recover_senders(fiber::PriorityPool &priority_pool, Block const &block)
{
    std::vector<std::optional<Address>> senders{block.transactions.size()};

    // there is a race internal to the promise so the lifetime needs to extend
    // past this function
    std::shared_ptr<boost::fibers::promise<void>[]> promises{
        new boost::fibers::promise<void>[block.transactions.size()]};

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        priority_pool.submit(
            i,
            [i,
             &sender = senders[i],
             promises,
             &transaction = block.transactions[i]] {
                sender = recover_sender(transaction);
                promises[i].set_value();
            });
    }

    for (unsigned i = 0; i < block.transactions.size(); ++i) {
        promises[i].get_future().wait();
    }
    return senders;
}

MONAD_NAMESPACE_END
