#pragma once

#include <category/vm/core/assert.h>

#include <iterator>
#include <optional>
#include <random>

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

    template <typename Engine, typename Action>
    void
    with_probability(Engine &eng, double const probability, Action &&action)
    {
        auto dist = std::uniform_real_distribution<double>(0.0, 1.0);
        auto const cutoff = dist(eng);

        if (probability >= cutoff) {
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
}
