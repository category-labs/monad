// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/core/byte_string.hpp>
#include <category/core/nibble.h>
#include <category/core/small_prng.hpp>
#include <category/mpt/db.hpp>
#include <category/mpt/merkle/compact_encode.hpp>
#include <category/mpt/nibbles_buffer.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>
#include <category/mpt/test/test_fixtures_base.hpp>
#include <category/mpt/update.hpp>

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <functional>
#include <limits>
#include <list>
#include <memory>
#include <string_view>
#include <utility>
#include <vector>

using namespace monad;
using namespace monad::mpt;

namespace
{
    constexpr unsigned repetitions = 5;
    constexpr size_t micro_iterations = 2'000'000;
    constexpr size_t key_pool = 1024;
    constexpr unsigned char state_nibble = 0;

    template <class T>
    void do_not_optimize(T const &value)
    {
        asm volatile("" : : "g"(&value) : "memory");
    }

    byte_string random_bytes(small_prng &rng, size_t const n)
    {
        byte_string out(n, 0);
        for (auto &b : out) {
            b = static_cast<unsigned char>(rng());
        }
        return out;
    }

    // Minimum over the repetitions, in nanoseconds per op.
    template <class F>
    double measure(size_t const ops, F &&run_once)
    {
        double best = std::numeric_limits<double>::max();
        for (unsigned r = 0; r < repetitions; ++r) {
            auto const ns = run_once();
            best = std::min(best, static_cast<double>(ns) / double(ops));
        }
        return best;
    }

    template <class Op>
    double measure_loop(Op &&op)
    {
        return measure(micro_iterations, [&] {
            auto const start = std::chrono::steady_clock::now();
            for (size_t i = 0; i < micro_iterations; ++i) {
                op(i);
            }
            auto const end = std::chrono::steady_clock::now();
            return std::chrono::duration_cast<std::chrono::nanoseconds>(
                       end - start)
                .count();
        });
    }

    struct Inputs
    {
        small_prng rng{0x6e696262};
        std::vector<byte_string> hashes;
        std::vector<byte_string> slots;
        Nibbles prefix1;
        Nibbles prefix65;
        byte_string path_bytes;
        byte_string cmp_a;
        byte_string cmp_b;
        byte_string cmp_diverge;
        byte_string cmp_shifted;

        Inputs()
        {
            for (size_t i = 0; i < key_pool; ++i) {
                hashes.push_back(random_bytes(rng, 32));
                slots.push_back(random_bytes(rng, 32));
            }
            prefix1 = concat(static_cast<unsigned char>(1));
            auto const block_id = random_bytes(rng, 32);
            prefix65 =
                concat(static_cast<unsigned char>(2), NibblesView{block_id});
            path_bytes = random_bytes(rng, 33);
            cmp_a = random_bytes(rng, 33);
            cmp_b = cmp_a;
            cmp_diverge = cmp_a;
            cmp_diverge[30] ^= 0xF0;
            // cmp_shifted viewed from nibble 1 equals cmp_a viewed from 0.
            cmp_shifted.assign(34, 0);
            for (unsigned i = 0; i < 66; ++i) {
                set_nibble(
                    cmp_shifted.data(), i + 1, get_nibble(cmp_a.data(), i));
            }
        }
    };

    struct Case
    {
        std::string_view name;
        std::function<double(Inputs &)> run;
    };

    double upsert_accounts(unsigned const slots_per_account)
    {
        constexpr size_t accounts_per_block = 1000;
        constexpr uint64_t blocks = 50;
        small_prng rng{0x75707372};
        return measure(accounts_per_block * blocks, [&] {
            Db db{std::make_unique<monad::test::StateMachineAlwaysMerkle>()};
            Node::SharedPtr root;
            int64_t total_ns = 0;
            for (uint64_t version = 0; version < blocks; ++version) {
                std::list<byte_string> bytes;
                std::list<Update> updates;
                UpdateList block;
                for (size_t a = 0; a < accounts_per_block; ++a) {
                    UpdateList storage;
                    for (unsigned s = 0; s < slots_per_account; ++s) {
                        auto const &key =
                            bytes.emplace_back(random_bytes(rng, 32));
                        auto const &value =
                            bytes.emplace_back(random_bytes(rng, 32));
                        storage.push_front(updates.emplace_back(make_update(
                            NibblesView{key},
                            value,
                            false,
                            UpdateList{},
                            version)));
                    }
                    auto const &key = bytes.emplace_back(random_bytes(rng, 32));
                    auto const &value =
                        bytes.emplace_back(random_bytes(rng, 40));
                    block.push_front(updates.emplace_back(make_update(
                        NibblesView{key},
                        value,
                        false,
                        std::move(storage),
                        version)));
                }
                auto const start = std::chrono::steady_clock::now();
                root = db.upsert(std::move(root), std::move(block), version);
                auto const end = std::chrono::steady_clock::now();
                total_ns +=
                    std::chrono::duration_cast<std::chrono::nanoseconds>(
                        end - start)
                        .count();
            }
            do_not_optimize(root);
            return total_ns;
        });
    }

    double compare_case(NibblesView const a, NibblesView const b)
    {
        return measure_loop([&](size_t) {
            do_not_optimize(a);
            do_not_optimize(b);
            auto const r = a <=> b;
            do_not_optimize(r);
        });
    }

    double compact_encode_case(NibblesView const path)
    {
        return measure_loop([&](size_t) {
            unsigned char out[64];
            do_not_optimize(path);
            auto const r = compact_encode(out, path, true);
            do_not_optimize(r);
            do_not_optimize(out);
        });
    }

    std::vector<Case> const cases = {
        {"concat_account_key",
         [](Inputs &in) {
             return measure_loop([&](size_t const i) {
                 auto const r = concat(
                     in.prefix1,
                     state_nibble,
                     NibblesView{in.hashes[i % key_pool]});
                 do_not_optimize(r);
             });
         }},
        {"concat_account_key_proposal",
         [](Inputs &in) {
             return measure_loop([&](size_t const i) {
                 auto const r = concat(
                     in.prefix65,
                     state_nibble,
                     NibblesView{in.hashes[i % key_pool]});
                 do_not_optimize(r);
             });
         }},
        {"concat_storage_key",
         [](Inputs &in) {
             return measure_loop([&](size_t const i) {
                 auto const r = concat(
                     in.prefix1,
                     state_nibble,
                     NibblesView{in.hashes[i % key_pool]},
                     NibblesView{in.slots[i % key_pool]});
                 do_not_optimize(r);
             });
         }},
        {"concat_branch_path_odd",
         [](Inputs &in) {
             NibblesView const path{1, 41, in.path_bytes.data()};
             return measure_loop([&](size_t const i) {
                 auto const r =
                     concat(static_cast<unsigned char>(i & 0xF), path);
                 do_not_optimize(r);
             });
         }},
        {"buffer_account_key",
         [](Inputs &in) {
             return measure_loop([&](size_t const i) {
                 NibblesBuffer const r{
                     in.prefix1,
                     state_nibble,
                     NibblesView{in.hashes[i % key_pool]}};
                 do_not_optimize(r);
             });
         }},
        {"buffer_account_key_proposal",
         [](Inputs &in) {
             return measure_loop([&](size_t const i) {
                 NibblesBuffer const r{
                     in.prefix65,
                     state_nibble,
                     NibblesView{in.hashes[i % key_pool]}};
                 do_not_optimize(r);
             });
         }},
        {"buffer_storage_key",
         [](Inputs &in) {
             return measure_loop([&](size_t const i) {
                 NibblesBuffer const r{
                     in.prefix1,
                     state_nibble,
                     NibblesView{in.hashes[i % key_pool]},
                     NibblesView{in.slots[i % key_pool]}};
                 do_not_optimize(r);
             });
         }},
        {"buffer_branch_path_odd",
         [](Inputs &in) {
             NibblesView const path{1, 41, in.path_bytes.data()};
             return measure_loop([&](size_t const i) {
                 NibblesBuffer const r{
                     static_cast<unsigned char>(i & 0xF), path};
                 do_not_optimize(r);
             });
         }},
        {"buffer_push_pop",
         [](Inputs &in) {
             NibblesView const path{1, 41, in.path_bytes.data()};
             NibblesBuffer b{NibblesView{0, 21, in.cmp_a.data()}};
             return measure_loop([&](size_t const i) {
                 b.push_back(static_cast<unsigned char>(i & 0xF));
                 b.append(path);
                 do_not_optimize(b);
                 b.shrink(21);
             });
         }},
        {"compare_equal_64_even",
         [](Inputs &in) {
             return compare_case(
                 NibblesView{0, 64, in.cmp_a.data()},
                 NibblesView{0, 64, in.cmp_b.data()});
         }},
        {"compare_equal_64_odd",
         [](Inputs &in) {
             return compare_case(
                 NibblesView{1, 65, in.cmp_a.data()},
                 NibblesView{1, 65, in.cmp_b.data()});
         }},
        {"compare_diverge_60_even",
         [](Inputs &in) {
             return compare_case(
                 NibblesView{0, 64, in.cmp_a.data()},
                 NibblesView{0, 64, in.cmp_diverge.data()});
         }},
        {"compare_mixed_parity_64",
         [](Inputs &in) {
             return compare_case(
                 NibblesView{0, 64, in.cmp_a.data()},
                 NibblesView{1, 65, in.cmp_shifted.data()});
         }},
        {"compact_encode_1_even",
         [](Inputs &in) {
             return compact_encode_case(
                 NibblesView{0, 1, in.path_bytes.data()});
         }},
        {"compact_encode_1_odd",
         [](Inputs &in) {
             return compact_encode_case(
                 NibblesView{1, 2, in.path_bytes.data()});
         }},
        {"compact_encode_31_even",
         [](Inputs &in) {
             return compact_encode_case(
                 NibblesView{0, 31, in.path_bytes.data()});
         }},
        {"compact_encode_31_odd",
         [](Inputs &in) {
             return compact_encode_case(
                 NibblesView{1, 32, in.path_bytes.data()});
         }},
        {"compact_encode_64_even",
         [](Inputs &in) {
             return compact_encode_case(
                 NibblesView{0, 64, in.path_bytes.data()});
         }},
        {"compact_encode_64_odd",
         [](Inputs &in) {
             return compact_encode_case(
                 NibblesView{1, 65, in.path_bytes.data()});
         }},
        {"upsert_accounts_1slot", [](Inputs &) { return upsert_accounts(1); }},
        {"upsert_accounts_4slots", [](Inputs &) { return upsert_accounts(4); }},
    };
}

// usage: nibbles_bench [case-substring]
int main(int const argc, char **const argv)
{
    std::string_view const filter = argc > 1 ? argv[1] : "";
    Inputs in;
    for (auto const &c : cases) {
        if (!filter.empty() && c.name.find(filter) == std::string_view::npos) {
            continue;
        }
        std::printf(
            "%.*s,%.1f\n", int(c.name.size()), c.name.data(), c.run(in));
        std::fflush(stdout);
    }
    return 0;
}
