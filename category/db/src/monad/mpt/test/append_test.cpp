#include "test_fixtures_base.hpp"
#include "test_fixtures_gtest.hpp"

#include <category/async/config.hpp>
#include <monad/mpt/config.hpp>
#include <monad/mpt/node.hpp>
#include <monad/mpt/update.hpp>

#include <category/core/test_util/gtest_signal_stacktrace_printer.hpp> // NOLINT

#include <iostream>
#include <vector>

using namespace MONAD_ASYNC_NAMESPACE;
using namespace MONAD_MPT_NAMESPACE;
using namespace monad::literals;

template <typename TFixture>
struct AppendTest : public TFixture
{
};

using AppendTestFastListOnly =
    monad::test::FillDBWithChunksGTest<monad::test::FillDBWithChunksConfig{
        .chunks_to_fill = 2, .alternate_slow_fast_writer = false}>;

using AppendTestTypes = ::testing::Types<AppendTestFastListOnly>;

TYPED_TEST_SUITE(AppendTest, AppendTestTypes);

TYPED_TEST(AppendTest, works)
{
    auto const last_root_version = this->state()->aux.db_history_max_version();
    auto const last_root_off = this->state()->aux.get_latest_root_offset();
    auto const last_slow_off =
        this->state()->aux.get_start_of_wip_slow_offset();
    auto const last_fast_off =
        this->state()->aux.get_start_of_wip_fast_offset();
    auto const root_hash_before = this->state()->root_hash();

    this->state()->keys.clear();
    this->state()->ensure_total_chunks(3);
    auto const root_hash_after1 = this->state()->root_hash();

    std::cout << "\nBefore rewind:";
    this->state()->print(std::cout);

    // Reset version, discarding all newer versions
    this->state()->aux.rewind_to_version(last_root_version);
    this->state()->version = last_root_version;
    EXPECT_EQ(last_root_off, this->state()->aux.get_latest_root_offset());
    EXPECT_EQ(last_slow_off, this->state()->aux.get_start_of_wip_slow_offset());
    EXPECT_EQ(last_fast_off, this->state()->aux.get_start_of_wip_fast_offset());

    // Get new current root
    this->state()->root = read_node_blocking(
        this->state()->aux, last_root_off, last_root_version);

    std::cout << "\nAfter rewind:";
    this->state()->print(std::cout);
    // Check number of chunks in use and current starting offsets are of the
    // same as before rewind
    EXPECT_EQ(this->state()->fast_list_ids().size(), 2);
    EXPECT_EQ(this->state()->aux.get_latest_root_offset(), last_root_off);
    EXPECT_EQ(this->state()->aux.get_start_of_wip_fast_offset(), last_fast_off);
    EXPECT_EQ(this->state()->aux.get_start_of_wip_slow_offset(), last_slow_off);
    EXPECT_EQ(
        this->state()->aux.node_writer_fast->sender().offset(), last_fast_off);
    EXPECT_EQ(
        this->state()->aux.node_writer_slow->sender().offset(), last_slow_off);

    // Has the root hash returned to what it should be?
    EXPECT_EQ(this->state()->root_hash(), root_hash_before);

    // Reinsert the same set of keys in `ensure_total_chunks(3)` earlier
    // Use the following snippet instead when async works with single read and
    // write buffer. Now have to limit upsert batch to not exhaust read buffers
    /*
    std::vector<Update> updates;
    updates.reserve(this->state()->keys.size());
    for (auto &e : this->state()->keys.size()) {
        updates.push_back(make_update(e.first, e.first));
    }
    */
    auto it = this->state()->keys.begin();
    while (it != this->state()->keys.end()) {
        std::vector<Update> updates;
        updates.reserve(1000);
        for (auto i = 0; i < 1000; ++i, ++it) {
            updates.push_back(make_update(it->first, it->first));
        }
        this->state()->root = upsert_vector(
            this->state()->aux,
            this->state()->sm,
            std::move(this->state()->root),
            std::move(updates),
            this->state()->version++);
    }

    auto const root_hash_after2 = this->state()->root_hash();
    // Has the root hash returned to what it should be?
    EXPECT_EQ(root_hash_after1, root_hash_after2);

    std::cout << "\nAfter append after rewind:";
    this->state()->print(std::cout);
}
