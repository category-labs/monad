// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#pragma once

#include <category/vm/core/assert.h>

#include <functional>
#include <iterator>
#include <optional>
#include <random>
#include <unordered_map>

namespace monad::vm::fuzzing
{
    namespace detail
    {
        template <typename Tuple, typename Func>
        void for_each_tuple(Tuple &&t, Func &&f)
        {
            [&]<std::size_t... Is>(std::index_sequence<Is...>) {
                (std::forward<Func>(f)(std::get<Is>(std::forward<Tuple>(t))),
                 ...);
            }(std::make_index_sequence<std::tuple_size_v<Tuple>>());
        }
    }

    template <typename Action>
    struct Choice
    {
        double probability;
        Action action;

        Choice(double p, Action a)
            : probability(p)
            , action(std::move(a))
        {
        }
    };

    template <
        typename Result, typename Engine, typename Default, typename... Choices>
    Result discrete_choice(Engine &eng, Default &&d, Choices &&...choices)
    {
        auto result = std::optional<Result>{};
        auto cumulative = 0.0;

        auto dist = std::uniform_real_distribution<double>(0.0, 1.0);
        auto const cutoff = dist(eng);

        detail::for_each_tuple(
            std::forward_as_tuple(
                choices..., Choice(1.0, std::forward<Default>(d))),
            [&](auto &&choice) {
                using Choice = decltype(choice);

                cumulative += std::forward<Choice>(choice).probability;
                if (!result && cumulative >= cutoff) {
                    result = Result{std::forward<Choice>(choice).action(eng)};
                }
            });

        MONAD_VM_DEBUG_ASSERT(result.has_value());
        return *result;
    }

    // Coin toss, biased whenever p != 0.5
    template <typename Engine>
    static bool toss(Engine &engine, double p)
    {
        std::bernoulli_distribution dist(p);
        return dist(engine);
    }

    template <typename Engine, typename Action>
    void
    with_probability(Engine &eng, double const probability, Action &&action)
    {
        if (toss(eng, probability)) {
            std::forward<Action>(action)(eng);
        }
    }

    template <typename Engine, std::random_access_iterator Iterator>
    auto const &uniform_sample(Engine &eng, Iterator begin, Iterator end)
    {
        using diff_t = std::iterator_traits<Iterator>::difference_type;

        MONAD_VM_DEBUG_ASSERT(begin != end);
        auto dist = std::uniform_int_distribution<diff_t>(0, end - begin - 1);
        return *(begin + dist(eng));
    }

    template <typename Engine, typename Container>
    auto const &uniform_sample(Engine &eng, Container const &in)
        requires(std::random_access_iterator<typename Container::iterator>)
    {
        return uniform_sample(eng, in.begin(), in.end());
    }

    template <
        typename T, typename Hash = std::hash<T>,
        typename Equal = std::equal_to<T>>
    class UniformSamplingSet
    {
    public:
        bool insert(T const &x)
        {
            auto const [_, ins] = map_.insert({x, vec_.size()});
            if (ins) {
                vec_.push_back(x);
            }
            return ins;
        }

        bool erase(T const &x)
        {
            auto const e = map_.find(x);
            if (e == map_.end()) {
                return false;
            }
            MONAD_VM_DEBUG_ASSERT(!vec_.empty());
            auto const i = e->second;
            map_.at(vec_.back()) = i;
            vec_[i] = vec_.back();
            vec_.pop_back();
            map_.erase(e);
            return true;
        }

        bool empty() const
        {
            return vec_.empty();
        }

        size_t size() const
        {
            return vec_.size();
        }

        bool contains(T const &x) const
        {
            return map_.contains(x);
        }

        template <typename Engine>
        T sample(Engine &eng)
        {
            MONAD_VM_ASSERT(!empty());
            return uniform_sample(eng, vec_);
        }

        void for_each(std::function<void(T const &)> f)
        {
            for (auto const &x : vec_) {
                f(x);
            }
        }

    private:
        std::unordered_map<T, size_t, Hash, Equal> map_;
        std::vector<T> vec_;
    };
}
