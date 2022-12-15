#include "helpers.hpp"

#include <gtest/gtest.h>

#include <monad/trie/in_memory_comparator.hpp>
#include <monad/trie/trie.hpp>

using namespace monad;
using namespace monad::trie;
using namespace evmc::literals;

template <>
inline auto injected_comparator<> = InMemoryPrefixPathComparator{};

TEST_F(in_memory_fixture, MultipleTrie)
{
    using namespace evmc::literals;

    // Add first trie
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000001_address);
    process_updates({
        make_upsert(
            0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        //               *
        make_upsert(
            0x1234567822345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe})),
        //               *
        make_upsert(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32,
            byte_string({0xde, 0xad, 0xca, 0xfe})),
        //                                                                      *
        make_upsert(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xba, 0xbe})),
    });

    EXPECT_EQ(
        trie_.root_hash(),
        0x3b71638660a388410706ca8b52d1008e979b47b1e938558004881b56a42c61c0_bytes32);

    // Add a second trie
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000002_address);
    process_updates(make_hard_updates());

    EXPECT_EQ(
        trie_.root_hash(),
        0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);

    // switch back to other and check that old root remains the same
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000001_address);
    EXPECT_EQ(
        trie_.root_hash(),
        0x3b71638660a388410706ca8b52d1008e979b47b1e938558004881b56a42c61c0_bytes32);

    // Remove from second trie
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000002_address);
    std::vector updates = {
        make_del(
            0x011b4d03dd8c01f1049143cf9c4c817e4b167f1d1b83e5c6f0f10d89ba1e7bce_bytes32),
        make_del(
            0x04f4a4a9c6d36d0a720cbbc0369a0f0c50f10553d5bf85cdce61efddab992c3c_bytes32),
        make_del(
            0x0f81fd306d0c0cddd0728a76e6bfb0dfa12891c89994d877f0445483563b380a_bytes32),
        make_del(
            0x184125b2e3d1ded2ad3f82a383d9b09bd5bac4ccea4d41092f49523399598aca_bytes32),
        make_del(
            0x1d8453ab2f7716504a4457ebe9831dbf996267e350ad0b2029f654d0dce1e055_bytes32),
        make_del(
            0x276d032750f286c508d060efcddd1b7a9becbfdb64efb5dfcbee057f86722fef_bytes32),
        make_del(
            0x2af357fc2ab2964b76482ec0fcac3b86f5aca1a8292676023c8b9ec392d821a0_bytes32),
        make_del(
            0x30e2bfdaad2f3c218a1a8cc54fa1c4e6182b6b7f3bca273390cf587b50b47311_bytes32),
        make_del(
            0x336c5ee8777d6ef07cafc1c552f7d0b579a7ae6e0af042e9d18981c5b78642d3_bytes32),
        make_del(
            0x39aebb35169c657d179f2c043aaa0f872996f17760662712f1dc6331fda57882_bytes32),
        make_del(
            0x3cac317908c699fe873a7f6ee4e8cd63fbe9918b2315c97be91585590168e301_bytes32),
        make_del(
            0x41414fecbcd48d24288f4cd69cdc4f11560667f16291c4c642082019a2c613a6_bytes32),
        make_del(
            0x44a25c9533b4c9e05472848068a6b5bcb693ce9e222f3f4ac82d2927a82a34ce_bytes32),
        make_del(
            0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21_bytes32),
        make_del(
            0x5037e1a5e02e081b1b850b130eca7ac17335fdf4c61cc5ff6ae765196fb0d5b3_bytes32),
        make_del(
            0x5380c7b7ae81a58eb98d9c78de4a1fd7fd9535fc953ed2be602daaa41767312a_bytes32),
        make_del(
            0x5429fdc28e48579bde709c0ca18c55d58f14c9438d5cd1829556be99fd68b97b_bytes32),
        make_del(
            0x5706de766d5661c754fb7b4c89db363309a9f89fa2945c9d8c7a303b79943963_bytes32),
        make_del(
            0x575b3e1ddd7d4ec1d0695cd1f4b1c0daa01cd98c8309e0d37422fa675d95c614_bytes32),
        make_del(
            0x5a657105c493a1213c976c653e929218bb4a516bca307dce5861ec23fffa4e58_bytes32),
        make_del(
            0x69a7b944221b2d0f646f2ce0d6fa665e124d14c473efc07ff1eb0c83454b4ae9_bytes32),
        make_del(
            0x74723bc3efaf59d897623890ae3912b9be3c4c67ccee3ffcf10b36406c722c1b_bytes32),
    };

    process_updates(updates);

    EXPECT_EQ(
        trie_.root_hash(),
        0x0835cc0ded52cfc5c950bf8f9f7daece213b5a679118f921578e8b164ab5f757_bytes32);

    // Remove first trie completely
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000001_address);

    process_updates({
        make_del(
            0x1234567812345678123456781234567812345678123456781234567812345678_bytes32),
        make_del(
            0x1234567822345678123456781234567812345678123456781234567812345678_bytes32),
        make_del(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32),
        make_del(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32),
    });
    EXPECT_EQ(
        trie_.root_hash(),
        0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421_bytes32);

    // Check that second remains the same
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000002_address);
    EXPECT_EQ(
        trie_.root_hash(),
        0x0835cc0ded52cfc5c950bf8f9f7daece213b5a679118f921578e8b164ab5f757_bytes32);
}

TEST_F(in_memory_fixture, MultipleTrieClear)
{
    using namespace evmc::literals;

    // Add first trie
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000001_address);
    process_updates({
        make_upsert(
            0x1234567812345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef})),
        //               *
        make_upsert(
            0x1234567822345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xbe, 0xef, 0xca, 0xfe, 0xba, 0xbe})),
        //               *
        make_upsert(
            0x1234567832345678123456781234567812345678123456781234567812345671_bytes32,
            byte_string({0xde, 0xad, 0xca, 0xfe})),
        //                                                                      *
        make_upsert(
            0x1234567832345678123456781234567812345678123456781234567812345678_bytes32,
            byte_string({0xde, 0xad, 0xba, 0xbe})),
    });

    EXPECT_EQ(
        trie_.root_hash(),
        0x3b71638660a388410706ca8b52d1008e979b47b1e938558004881b56a42c61c0_bytes32);

    // Add a second trie
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000002_address);
    process_updates(make_hard_updates());

    EXPECT_EQ(
        trie_.root_hash(),
        0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);

    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000001_address);
    clear();

    EXPECT_EQ(trie_.root_hash(), NULL_ROOT);

    // Check that second remains the same
    trie_.set_trie_prefix(0xc9ea7ed000000000000000000000000000000002_address);
    EXPECT_EQ(
        trie_.root_hash(),
        0xcbb6d81afdc76fec144f6a1a283205d42c03c102a94fc210b3a1bcfdcb625884_bytes32);

    clear();
    EXPECT_EQ(trie_.root_hash(), NULL_ROOT);

    EXPECT_TRUE(storage_empty());
}
