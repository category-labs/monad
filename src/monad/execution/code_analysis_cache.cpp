#include <monad/config.hpp>
#include <monad/core/assert.h>
#include <monad/core/unaligned.hpp>
#include <monad/execution/code_analysis_cache.hpp>

#include <boost/intrusive/list.hpp>
#include <boost/intrusive/unordered_set.hpp>

#include <cstddef>
#include <memory>
#include <mutex>
#include <type_traits>
#include <utility>

using namespace evmone::baseline;

MONAD_NAMESPACE_BEGIN

class CodeAnalysisCache::Impl
{
    using ListHook =
        boost::intrusive::list_member_hook<boost::intrusive::link_mode<
            boost::intrusive::link_mode_type::normal_link>>;

    static_assert(sizeof(ListHook) == 16);
    static_assert(alignof(ListHook) == 8);

    using SetHook =
        boost::intrusive::unordered_set_member_hook<boost::intrusive::link_mode<
            boost::intrusive::link_mode_type::normal_link>>;

    static_assert(sizeof(SetHook) == 8);
    static_assert(alignof(SetHook) == 8);

    struct Item
    {
        bytes32_t hash{};
        std::shared_ptr<CodeAnalysis> analysis{};

        ListHook list_hook{};
        SetHook set_hook{};
    };

    static_assert(sizeof(Item) == 72);
    static_assert(alignof(Item) == 8);

    using List = boost::intrusive::list<
        Item, boost::intrusive::member_hook<Item, ListHook, &Item::list_hook>,
        boost::intrusive::constant_time_size<true>>;

    static_assert(sizeof(List) == 24);
    static_assert(alignof(List) == 8);

    struct HashFunc
    {
        [[gnu::always_inline]] constexpr size_t
        operator()(bytes32_t const &hash) const
        {
            return unaligned_load<size_t>(hash.bytes);
        }
    };

    struct KeyFunc
    {
        typedef bytes32_t type;

        [[gnu::always_inline]] constexpr bytes32_t const &
        operator()(Item const &item) const
        {
            return item.hash;
        }
    };

    using Set = boost::intrusive::unordered_set<
        Item, boost::intrusive::member_hook<Item, SetHook, &Item::set_hook>,
        boost::intrusive::constant_time_size<false>,
        boost::intrusive::hash<HashFunc>,
        boost::intrusive::power_2_buckets<true>,
        boost::intrusive::incremental<true>,
        boost::intrusive::key_of_value<KeyFunc>>;

    static_assert(sizeof(Set) == 24);
    static_assert(alignof(Set) == 8);

    static_assert(std::is_same_v<Set::key_type, bytes32_t>);

    static constexpr size_t N = 1024;

    mutable std::mutex mutex_;

    Item items_[N]{};
    size_t n_{0};

    List list_{};
    Set::bucket_type set_buckets_[N];
    Set set_{Set::bucket_traits(set_buckets_, N)};

    std::pair<size_t, size_t> hit_rate_{0, 0};

public:
    Impl() = default;

    [[gnu::always_inline]] std::pair<size_t, size_t> hit_rate() const
    {
        std::unique_lock ulk(mutex_);
        MONAD_ASSERT(ulk.owns_lock());
        return hit_rate_;
    };

    [[gnu::always_inline]] std::shared_ptr<CodeAnalysis>
    get(bytes32_t const &hash)
    {
        std::unique_lock ulk(mutex_);
        MONAD_ASSERT(ulk.owns_lock());
        auto const it = set_.find(hash);
        if (it == set_.end()) {
            ++hit_rate_.second;
            return nullptr;
        }
        ++hit_rate_.first;
        ++hit_rate_.second;
        list_.erase(list_.iterator_to(*it));
        list_.push_front(*it);
        return it->analysis;
    }

    [[gnu::always_inline]] std::shared_ptr<CodeAnalysis>
    put(bytes32_t const &hash, CodeAnalysis &&analysis)
    {
        std::unique_lock ulk(mutex_);
        MONAD_ASSERT(ulk.owns_lock());
        Item *item = nullptr;
        if (n_ < N) {
            item = &items_[n_++];
        }
        else {
            item = &list_.back();
            list_.pop_back();
            set_.erase(item->hash);
            item->analysis.reset();
        }
        MONAD_DEBUG_ASSERT(item);
        item->hash = hash;
        item->analysis = std::make_shared<CodeAnalysis>(std::move(analysis));
        list_.push_front(*item);
        auto const [it, inserted] = set_.insert(*item);
        MONAD_DEBUG_ASSERT(inserted);
        return it->analysis;
    }
};

CodeAnalysisCache::CodeAnalysisCache()
    : impl_(std::make_unique<Impl>())
{
}

CodeAnalysisCache::~CodeAnalysisCache() {}

std::shared_ptr<CodeAnalysis> CodeAnalysisCache::get(bytes32_t const &hash)
{
    return impl_->get(hash);
}

std::shared_ptr<CodeAnalysis>
CodeAnalysisCache::put(bytes32_t const &hash, CodeAnalysis &&analysis)
{
    return impl_->put(hash, std::move(analysis));
}

std::pair<size_t, size_t> CodeAnalysisCache::hit_rate() const
{
    return impl_->hit_rate();
}

MONAD_NAMESPACE_END
