#include <monad/mpt/config.hpp>

MONAD_MPT_NAMESPACE_BEGIN

// Turn on to collect stats
#define MONAD_MPT_COLLECT_STATS 1

namespace detail
{
    struct TrieUpdateCollectedStats
    {
#ifdef MONAD_MPT_COLLECT_STATS
        // counters
        unsigned nodes_created_or_updated{0};
        // reads stats
        unsigned nreads_compaction{0};
        // [0]: fast, [1]: slow
        unsigned nreads_before_compact_offset[2] = {0, 0};
        unsigned nreads_after_compact_offset[2] = {0, 0};
        unsigned bytes_read_before_compact_offset[2] = {0, 0};
        unsigned bytes_read_after_compact_offset[2] = {0, 0};

        // node copy stats
        unsigned compacted_nodes_in_fast{0}; // fast to slow
        unsigned compacted_nodes_in_slow{0}; // slow to slow
        unsigned nodes_copied_fast_to_fast_for_fast{0};
        unsigned nodes_copied_fast_to_fast_for_slow{0};
        unsigned nodes_copied_slow_to_fast_for_slow{0};

        // bytes copied stats
        // Sum of the following three equals the current block slow ring
        // growth
        unsigned compacted_bytes_in_fast{0}; // copied from fast to slow
        unsigned compacted_bytes_in_slow{0}; // copied from slow to slow
        unsigned bytes_copied_slow_to_fast_for_slow{0};

        // expire stats
        unsigned nodes_updated_expire{0};
        unsigned nreads_expire{0};
#else
        unsigned compacted_bytes_in_slow{0};
        char padding[4];
#endif

        void reset()
        {
            this->~TrieUpdateCollectedStats();
            new (this) TrieUpdateCollectedStats();
        }
    };

#ifdef MONAD_MPT_COLLECT_STATS
    static_assert(sizeof(TrieUpdateCollectedStats) == 80);
#else
    static_assert(sizeof(TrieUpdateCollectedStats) == 8);
#endif
    static_assert(alignof(TrieUpdateCollectedStats) == 4);
    static_assert(std::is_trivially_copyable_v<TrieUpdateCollectedStats>);
}

MONAD_MPT_NAMESPACE_END
