#include "benchmarktest.hpp"

#include "statetest.hpp"
#include "transaction.hpp"

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <istream>
#include <string>
#include <vector>

namespace json = nlohmann;

namespace monad::test
{
    using namespace evmone::test;

    namespace
    {
        TestBlock load_test_block(json::json const &j)
        {
            using namespace evmone::state;
            TestBlock tb;

            if (auto it = j.find("transactions"); it != j.end()) {
                for (auto const &tx : *it) {
                    tb.transactions.emplace_back(from_json<Transaction>(tx));
                }
            }

            return tb;
        }

        BenchmarkTest
        load_benchmark_test_case(std::string const &name, json::json const &j)
        {
            using namespace evmone::state;

            BenchmarkTest bt;
            bt.name = name;
            bt.pre_state = from_json<TestState>(j.at("pre"));

            for (auto const &el : j.at("blocks")) {
                bt.test_blocks.emplace_back(load_test_block(el));
            }

            return bt;
        }

    } // namespace

    static void from_json(json::json const &j, std::vector<BenchmarkTest> &o)
    {
        for (auto const &elem_it : j.items()) {
            o.emplace_back(
                load_benchmark_test_case(elem_it.key(), elem_it.value()));
        }
    }

    std::vector<BenchmarkTest> load_benchmark_tests(std::istream &input)
    {
        return json::json::parse(input).get<std::vector<BenchmarkTest>>();
    }

} // namespace monad::test
