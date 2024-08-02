#include <monad/mpt/config.hpp>

MONAD_MPT_NAMESPACE_BEGIN

// Turn on to collect stats
#define MONAD_MPT_COLLECT_STATS 1

namespace detail
{
    struct TrieUpdateCollectedStats
    {
        unsigned num_nodes_created{0};
        // counters
        unsigned num_nodes_copied{0};
        unsigned num_compaction_reads{0};
        unsigned nodes_copied_from_fast_to_slow{0};
        unsigned nodes_copied_from_fast_to_fast{0};
        unsigned nodes_copied_from_slow_to_slow{0};
        // [0]: fast, [1]: slow
        unsigned nreads_before_offset[2] = {0, 0};
        unsigned nreads_after_offset[2] = {0, 0};
        unsigned bytes_read_before_offset[2] = {0, 0};
        unsigned bytes_read_after_offset[2] = {0, 0};
        unsigned nodes_copied_for_compacting_slow = 0;
        unsigned nodes_copied_for_compacting_fast = 0;

        void reset()
        {
            this->~TrieUpdateCollectedStats();
            new (this) TrieUpdateCollectedStats();
        }
    };

    static_assert(sizeof(TrieUpdateCollectedStats) == 64);
    static_assert(alignof(TrieUpdateCollectedStats) == 4);
    static_assert(std::is_trivially_copyable_v<TrieUpdateCollectedStats>);
}

MONAD_MPT_NAMESPACE_END
