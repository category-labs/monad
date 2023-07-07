#include <monad/test/one_hundred_updates.hpp>
#include <monad/test/trie_fixture.hpp>

#include <gtest/gtest.h>

#include <monad/trie/in_memory_comparator.hpp>
#include <monad/trie/rocks_comparator.hpp>
#include <monad/trie/trie.hpp>

#include <random>

using namespace monad;
using namespace monad::trie;
using namespace evmc::literals;

namespace
{
    template <typename T>
    T basic_node(std::optional<size_t> key_size, byte_string path_to_node)
    {
        T node;
        node.key_size = key_size;
        node.path_to_node = Nibbles(path_to_node);
        return node;
    }

    bool validate_list(auto const &list, auto const &expected)
    {
        return std::ranges::equal(
            list, expected, [](auto const &a, auto const &b) {
                return std::visit(
                    overloaded{
                        [](Leaf na, Leaf nb) {
                            return na.path_to_node == nb.path_to_node &&
                                   na.key_size == nb.key_size;
                        },
                        [](Branch na, Branch nb) {
                            return na.path_to_node == nb.path_to_node &&
                                   na.key_size == nb.key_size;
                        },
                        [](auto, auto) { return false; }},
                    a,
                    b);
            });
    }
}

template <typename TBase>
class GenerateTransformationListFixture : public TBase
{
public:
    using TBase::process_updates;

    GenerateTransformationListFixture()
    {
        process_updates({
            test::make_upsert(
                Nibbles(byte_string{0x04, 0x02, 0x02, 0x01}), {0xff}),
            test::make_upsert(
                Nibbles(byte_string{0x04, 0x02, 0x03, 0x02}), {0xff}),
            test::make_upsert(
                Nibbles(byte_string{0x04, 0x02, 0x03, 0x06}), {0xff}),
            test::make_upsert(
                Nibbles(byte_string{0x04, 0x05, 0x02, 0x01}), {0xff}),
        });
    }
};

template <typename TBase>
class TrieUpdateFixture : public TBase
{
public:
    using TBase::process_updates;

    TrieUpdateFixture()
    {
        process_updates({
            test::make_upsert(
                0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
                byte_string({0xde, 0xad, 0xbe, 0xef})),
            //               *
            test::make_upsert(
                0x1234567822345678123456781234567812345678123456781234567812345678_bytes32,
                byte_string({0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe})),
            //               *
            test::make_upsert(
                0x1234567832345678123456781234567812345678123456781234567812345671_bytes32,
                byte_string({0xde, 0xad, 0xca, 0xfe})),
            //                                                                      *
            test::make_upsert(
                0x1234567832345678123456781234567812345678123456781234567812345678_bytes32,
                byte_string({0xde, 0xad, 0xba, 0xbe})),
        });
    }
};

using rocks_fixture_t = test::rocks_fixture<PathComparator>;
using in_memory_fixture_t = test::in_memory_fixture<InMemoryPathComparator>;

template <typename TFixture>
struct GenerateTransformationListTest : public TFixture
{
};
using GenerateTransformationListTypes = ::testing::Types<
    GenerateTransformationListFixture<rocks_fixture_t>,
    GenerateTransformationListFixture<in_memory_fixture_t>>;
TYPED_TEST_SUITE(
    GenerateTransformationListTest, GenerateTransformationListTypes);

template <typename TFixture>
struct TrieUpdateTest : public TFixture
{
};
using TrieUpdateTypes = ::testing::Types<
    TrieUpdateFixture<rocks_fixture_t>, TrieUpdateFixture<in_memory_fixture_t>>;
TYPED_TEST_SUITE(TrieUpdateTest, TrieUpdateTypes);

template <typename TFixture>
struct BasicTrieTest : public TFixture
{
};
using BasicTrieTypes = ::testing::Types<rocks_fixture_t, in_memory_fixture_t>;
TYPED_TEST_SUITE(BasicTrieTest, BasicTrieTypes);

TYPED_TEST(BasicTrieTest, EmptyTrie)
{
    EXPECT_EQ(
        this->trie_.root_hash(),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32);
}

TYPED_TEST(BasicTrieTest, OneElement)
{
    std::vector updates = {test::make_upsert(
        0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
        byte_string({0xde, 0xad, 0xbe, 0xef}))};
    this->process_updates(updates);

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x9e586b00a955a1e3d24961ff0311d9cba844136213759880c08f77ecb1b70b7e_bytes32);

    // update it again
    updates = {test::make_upsert(
        0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
        byte_string({0xde, 0xad}))};
    this->process_updates(updates);

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x3622cef16d065ca02d848a6548f6dc4c2181d1bb1b9ad21eec3da906780ca709_bytes32);
}

TYPED_TEST(BasicTrieTest, Simple)
{
    std::vector updates = {
        test::make_upsert(
            0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x1234567822345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe})),
        test::make_upsert(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32,
            byte_string({0xde, 0xad, 0xca, 0xfe})),
        test::make_upsert(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xba, 0xbe})),
    };
    this->process_updates(updates);

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x3b71638660a388410706ca8b52d1008e979b47b1e938558004881b56a42c61c0_bytes32);
}

TYPED_TEST(BasicTrieTest, UnrelatedLeaves)
{
    std::vector updates = {
        test::make_upsert(
            0x0234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x2234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x3234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
    };
    this->process_updates(updates);

    EXPECT_EQ(
        this->trie_.root_hash(),
        0xa17471d2db79edac8d01de8737cbf7d03ea962bafe3d759f61040fc0ded5fad9_bytes32);
}

TYPED_TEST(TrieUpdateTest, None)
{
    EXPECT_EQ(
        this->trie_.root_hash(),
        0x3b71638660a388410706ca8b52d1008e979b47b1e938558004881b56a42c61c0_bytes32);
}

TYPED_TEST(TrieUpdateTest, RemoveEverything)
{
    this->process_updates({
        test::make_del(
            0x1234567812345678123456781234567812345678123456781234567812345678_bytes32),
        test::make_del(
            0x1234567822345678123456781234567812345678123456781234567812345678_bytes32),
        test::make_del(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32),
        test::make_del(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32),
    });

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32);
}

TYPED_TEST(TrieUpdateTest, DeleteSingleBranch)
{
    this->process_updates({
        test::make_del(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32),
        test::make_del(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32),
    });

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x3d32d5e1b401520d20cde4cc7db33b8a23f18d0c783bb9dd1462fa6dc753a48a_bytes32);
}

TYPED_TEST(TrieUpdateTest, Simple)
{
    this->process_updates({
        test::make_upsert(
            0x0234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x1234567802345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x1234567822345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xef, 0xca, 0xfe, 0xba, 0xbe})),
        test::make_del(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32),
        test::make_del(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32),
    });

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x44227d20c84dd2c72431ecaef175e78b9a5539f55ddfe3bc9bae5331172d605c_bytes32);
}

TYPED_TEST(GenerateTransformationListTest, OneUpdate)
{
    // ----------------------------------------------------------------

    std::vector updates = {test::make_upsert(
        Nibbles(byte_string({0x05, 0x05, 0x05, 0x05})), {0xff})};

    std::list<Node> expected = {
        basic_node<Branch>(0, {0x04}),
        basic_node<Leaf>(std::nullopt, {0x05, 0x05, 0x05, 0x05})};

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {test::make_upsert(
        Nibbles(byte_string({0x03, 0x03, 0x03, 0x03})), {0xff})};

    expected = std::list<Node>({
        basic_node<Leaf>(std::nullopt, {0x03, 0x03, 0x03, 0x03}),
        basic_node<Branch>(0, {0x04}),
    });

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {test::make_upsert(
        Nibbles(byte_string({0x04, 0x06, 0x02, 0x01})), {0xff})};

    expected = std::list<Node>(
        {basic_node<Branch>(0, {0x04}),
         basic_node<Leaf>(std::nullopt, {0x04, 0x06, 0x02, 0x01})});

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {test::make_upsert(
        Nibbles(byte_string({0x04, 0x05, 0x02, 0x02})), {0xff})};

    expected = std::list<Node>(
        {basic_node<Branch>(2, {0x04, 0x02}),
         basic_node<Leaf>(2, {0x04, 0x05, 0x02, 0x01}),
         basic_node<Leaf>(std::nullopt, {0x04, 0x05, 0x02, 0x02})});

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {test::make_upsert(
        Nibbles(byte_string({0x04, 0x02, 0x03, 0x04})), {0xff})};

    expected = std::list<Node>({
        basic_node<Leaf>(3, {0x04, 0x02, 0x02, 0x01}),
        basic_node<Leaf>(4, {0x04, 0x02, 0x03, 0x02}),
        basic_node<Leaf>(std::nullopt, {0x04, 0x02, 0x03, 0x04}),
        basic_node<Leaf>(4, {0x04, 0x02, 0x03, 0x06}),
        basic_node<Leaf>(2, {0x04, 0x05, 0x02, 0x01}),
    });

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));
}

TYPED_TEST(GenerateTransformationListTest, MultipleUpdates)
{
    // ----------------------------------------------------------------

    std::vector updates = {
        test::make_upsert(
            Nibbles(byte_string({0x04, 0x02, 0x02, 0x01})), {0xff}),
        test::make_del(Nibbles(byte_string({0x04, 0x02, 0x03, 0x06})))};

    std::vector<Node> expected = {
        basic_node<Leaf>(std::nullopt, {0x04, 0x02, 0x02, 0x01}),
        basic_node<Leaf>(4, {0x04, 0x02, 0x03, 0x02}),
        basic_node<Leaf>(2, {0x04, 0x05, 0x02, 0x01})};

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {
        test::make_del(Nibbles(byte_string({0x04, 0x02, 0x03, 0x02}))),
        test::make_upsert(
            Nibbles(byte_string({0x04, 0x02, 0x03, 0x03})), {0xff}),
    };

    expected = std::vector<Node>(
        {basic_node<Leaf>(3, {0x04, 0x02, 0x02, 0x01}),
         basic_node<Leaf>(std::nullopt, {0x04, 0x02, 0x03, 0x03}),
         basic_node<Leaf>(4, {0x04, 0x02, 0x03, 0x06}),
         basic_node<Leaf>(2, {0x04, 0x05, 0x02, 0x01})});

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {
        test::make_del(Nibbles(byte_string({0x04, 0x02, 0x02, 0x01}))),
        test::make_del(Nibbles(byte_string({0x04, 0x02, 0x03, 0x02}))),
        test::make_del(Nibbles(byte_string({0x04, 0x02, 0x03, 0x06}))),
        test::make_del(Nibbles(byte_string({0x04, 0x05, 0x02, 0x01}))),
    };

    expected.clear();

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));

    // ----------------------------------------------------------------

    updates = {
        test::make_upsert(
            Nibbles(byte_string({0x04, 0x02, 0x02, 0x00})), {0xff}),
        test::make_upsert(
            Nibbles(byte_string({0x04, 0x02, 0x03, 0x07})), {0xff}),
        test::make_del(Nibbles(byte_string({0x04, 0x05, 0x02, 0x01}))),
    };

    expected = std::vector<Node>({
        basic_node<Leaf>(std::nullopt, {0x04, 0x02, 0x02, 0x00}),
        basic_node<Leaf>(3, {0x04, 0x02, 0x02, 0x01}),
        basic_node<Branch>(3, {0x04, 0x02, 0x03}),
        basic_node<Leaf>(std::nullopt, {0x04, 0x02, 0x03, 0x07}),
    });

    EXPECT_TRUE(validate_list(
        this->trie_.generate_transformation_list(updates), expected));
}

TYPED_TEST(BasicTrieTest, HardOnlyUpserts)
{
    auto const hard_updates = test::make_updates(test::one_hundred_updates);
    auto it = hard_updates.begin();

    std::vector<std::vector<Update>> updates;

    // Batch updates into groups
    while (it != hard_updates.end()) {
        auto end = std::distance(it, hard_updates.end()) < 19
                       ? hard_updates.end()
                       : std::next(it, 19);
        updates.push_back({it, end});
        it = end;
    }

    // Randomize the updates
    auto rng = std::default_random_engine{10};
    std::shuffle(updates.begin(), updates.end(), rng);

    for (auto const &update : updates) {
        this->process_updates(update);
    }

    EXPECT_EQ(
        this->trie_.root_hash(),
        0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);
}

TYPED_TEST(BasicTrieTest, HardWithRemoval)
{
    this->process_updates(test::make_updates(test::one_hundred_updates));
    EXPECT_EQ(
        this->trie_.root_hash(),
        0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);

    std::vector updates = {
        test::make_del(
            0x011b4d03dd8c01f1049143cf9c4c817e4b167f1d1b83e5c6f0f10d89ba1e7bce_bytes32),
        test::make_del(
            0x04f4a4a9c6d36d0a720cbbc0369a0f0c50f10553d5bf85cdce61efddab992c3c_bytes32),
        test::make_del(
            0x0f81fd306d0c0cddd0728a76e6bfb0dfa12891c89994d877f0445483563b380a_bytes32),
        test::make_del(
            0x184125b2e3d1ded2ad3f82a383d9b09bd5bac4ccea4d41092f49523399598aca_bytes32),
        test::make_del(
            0x1d8453ab2f7716504a4457ebe9831dbf996267e350ad0b2029f654d0dce1e055_bytes32),
        test::make_del(
            0x276d032750f286c508d060efcddd1b7a9becbfdb64efb5dfcbee057f86722fef_bytes32),
        test::make_del(
            0x2af357fc2ab2964b76482ec0fcac3b86f5aca1a8292676023c8b9ec392d821a0_bytes32),
        test::make_del(
            0x30e2bfdaad2f3c218a1a8cc54fa1c4e6182b6b7f3bca273390cf587b50b47311_bytes32),
        test::make_del(
            0x336c5ee8777d6ef07cafc1c552f7d0b579a7ae6e0af042e9d18981c5b78642d3_bytes32),
        test::make_del(
            0x39aebb35169c657d179f2c043aaa0f872996f17760662712f1dc6331fda57882_bytes32),
        test::make_del(
            0x3cac317908c699fe873a7f6ee4e8cd63fbe9918b2315c97be91585590168e301_bytes32),
        test::make_del(
            0x41414fecbcd48d24288f4cd69cdc4f11560667f16291c4c642082019a2c613a6_bytes32),
        test::make_del(
            0x44a25c9533b4c9e05472848068a6b5bcb693ce9e222f3f4ac82d2927a82a34ce_bytes32),
        test::make_del(
            0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21_bytes32),
        test::make_del(
            0x5037e1a5e02e081b1b850b130eca7ac17335fdf4c61cc5ff6ae765196fb0d5b3_bytes32),
        test::make_del(
            0x5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a_bytes32),
        test::make_del(
            0x5429fdc28e48579bde709c0ca18c55d58f14c9438d5cd1829556be99fd68b97b_bytes32),
        test::make_del(
            0x5706de766d5661c754fb7b4c89db363309a9f89fa2945c9d8c7a303b79943963_bytes32),
        test::make_del(
            0x575b3e1ddd7d4ec1d0695cd1f4b1c0daa01cd98c8309e0d37422fa675d95c614_bytes32),
        test::make_del(
            0x5a657105c493a1213c976c653e929218bb4a516bca307dce5861ec23fffa4e58_bytes32),
        test::make_del(
            0x69a7b944221b2d0f646f2ce0d6fa665e124d14c473efc07ff1eb0c83454b4ae9_bytes32),
        test::make_del(
            0x74723bc3efaf59d897623890ae3912b9be3c4c67ccee3ffcf10b36406c722c1b_bytes32),
    };

    this->process_updates(updates);

    EXPECT_EQ(
        this->trie_.root_hash(),
        0x0835cc0ded52cfc5c950bf8f9f7daece213b5a679118f921578e8b164ab5f757_bytes32);
}

TYPED_TEST(BasicTrieTest, StateCleanup)
{
    auto const verify = [&](auto const &e) {
        this->trie_cursor_.lower_bound({});
        for (auto const &expected : e) {
            EXPECT_TRUE(this->trie_cursor_.valid());
            EXPECT_EQ(this->trie_cursor_.key()->path(), expected);
            this->trie_cursor_.next();
        }

        // should be at the end now
        EXPECT_FALSE(this->trie_cursor_.valid());
    };

    this->process_updates({
        test::make_upsert(Nibbles(byte_string({0x01, 0x02, 0x0, 0x0})), {0xff}),
        test::make_upsert(Nibbles(byte_string({0x01, 0x02, 0x3, 0x4})), {0xff}),
        test::make_upsert(Nibbles(byte_string({0x01, 0x02, 0x3, 0x5})), {0xff}),
    });

    std::vector expected_storage = {
        Nibbles(),
        Nibbles(byte_string{0x01, 0x02, 0x00}),
        Nibbles(byte_string{0x01, 0x02, 0x03}),
        Nibbles(byte_string{0x01, 0x02, 0x03, 0x04}),
        Nibbles(byte_string{0x01, 0x02, 0x03, 0x05}),
    };

    verify(expected_storage);

    this->process_updates({
        test::make_del(Nibbles(byte_string{0x01, 0x02, 0x03, 0x04})),
    });

    expected_storage = {
        Nibbles(),
        Nibbles(byte_string{0x01, 0x02, 0x00}),
        Nibbles(byte_string{0x01, 0x02, 0x03})};

    verify(expected_storage);
}

TYPED_TEST(BasicTrieTest, KeyOfUpdatedNodeChanges)
{
    this->process_updates({
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000000_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000001_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
    });

    this->process_updates({
        test::make_del(
            0x0000000000000000000000000000000000000000000000000000000000000000_bytes32),
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000001_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
    });

    this->process_updates({test::make_upsert(
        0x0000000000000000000000000000000000000000000000000000000000000000_bytes32,
        byte_string({0xde, 0xad, 0xbe, 0xef}))});
}

TYPED_TEST(BasicTrieTest, BranchDeletedAfterSiblingGetsDeleted)
{
    this->process_updates({
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000110_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000111_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000120_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
    });

    this->process_updates(
        {test::make_upsert(
             0x0000000000000000000000000000000000000000000000000000000000000111_bytes32,
             byte_string({0xde, 0xad, 0xbe, 0xef})),
         test::make_del(
             0x0000000000000000000000000000000000000000000000000000000000000120_bytes32)});

    this->process_updates({
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000130_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
    });
}

TYPED_TEST(BasicTrieTest, InsertingOtherNodesAndDeletingRoot)
{
    this->process_updates({
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000120_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
    });

    this->process_updates({
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000110_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_upsert(
            0x0000000000000000000000000000000000000000000000000000000000000111_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        test::make_del(
            0x0000000000000000000000000000000000000000000000000000000000000120_bytes32),
    });
}
