#include <monad/rlp/decode_helpers.hpp>

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>

#include <filesystem>
#include <fstream>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::rlp;

inline byte_string read_block_asset(uint32_t block_num)
{
    auto monad_path = std::filesystem::current_path()
                        .parent_path()
                        .parent_path()
                        .parent_path()
                        .parent_path()
                        .parent_path();
    auto path = monad_path
                / "src"
                / "monad"
                / "rlp"
                / "test"
                / "assets"
                / "block_encodings"
                / std::to_string(block_num);
    

    std::ifstream input(path.c_str(),std::ios::binary);

    byte_string output;
    char buf;

    // glee: there probably is a more correct way to do this...
    if (input)
    {
        while (input.read(&buf, 1))
        {
            output += buf;
        }
        output = output.substr(0,output.length()-1);
    }

    return output;
}

TEST(Rlp_Account, DecodeBlock1)
{
    byte_string block_encoding = read_block_asset(2730000);
    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding,pos);

    // Header
    {
        EXPECT_EQ(block.header.parent_hash, 0x18057c6cc208419928dbf4891af02d865f5d72f34f1880a3a3674b6a2585d8ec_bytes32);
        EXPECT_EQ(block.header.ommers_hash, 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32);
        EXPECT_EQ(block.header.beneficiary, 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address);
        EXPECT_EQ(block.header.state_root, 0xbda8c4941b104eb8b2a698eef53e5bfa63f40b7497f2426a619623a82bdbfacd_bytes32);
        // How to get the transaction root & receipt root & bloom of the block?
        //EXPECT_EQ(block.hedaer.transaction_root, )
        EXPECT_EQ(block.header.difficulty, 71133750415151);
        EXPECT_EQ(block.header.number, 2730000);
        EXPECT_EQ(block.header.gas_limit, 3'293'766);
        EXPECT_EQ(block.header.gas_used, 84'000);
        EXPECT_EQ(block.header.timestamp, 1480625618); // https://planetcalc.com/7157/
        EXPECT_EQ(block.header.extra_data, byte_string({0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69, 0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31}));
        // How to find the mixHash of the block?
        EXPECT_EQ(block.header.nonce, byte_string_fixed<8UL>({0x5b,0x75, 0xd1, 0x38, 0x22, 0xb5, 0xe1, 0xd4}));
    }

    // Transactions:
    {
        using namespace intx;
        // Transactions[0]
        {
            EXPECT_EQ(block.transactions[0].nonce, 1'639'528);
            EXPECT_EQ(block.transactions[0].gas_price, 25'000'000'000); // 25Gwei
            EXPECT_EQ(block.transactions[0].gas_limit, 90'000);
            EXPECT_EQ(*block.transactions[0].to, 0xbb474edbc0c6ecf5c0455f8e6f90b8d46098e016_address);
            EXPECT_EQ(block.transactions[0].amount, 0x03dd59a7fca63400_u128); // 278477330000000000 Wei
            EXPECT_EQ(block.transactions[0].data, byte_string{});
            // Need to figure out the Signature Chain Stuff
        }
        // Transactions[1]
        {
            EXPECT_EQ(block.transactions[1].nonce, 886'728);
            EXPECT_EQ(block.transactions[1].gas_price, 20'000'000'000); // 20Gwei
            EXPECT_EQ(block.transactions[1].gas_limit, 90'000);
            EXPECT_EQ(*block.transactions[1].to, 0x288e49edb33a4b88860e8ce10a0407eaefd7dfda_address);
            EXPECT_EQ(block.transactions[1].amount,0x6EF6DD445B94970_u128);
            EXPECT_EQ(block.transactions[1].data, byte_string{});
            // Need to figure out the Signature Chain Stuff
        }
        // Transactions[2]
        {
            EXPECT_EQ(block.transactions[2].nonce, 1'639'529);
            EXPECT_EQ(block.transactions[2].gas_price, 25'000'000'000); // 25Gwei
            EXPECT_EQ(block.transactions[2].gas_limit, 90'000);
            EXPECT_EQ(*block.transactions[2].to, 0xa7895d323bfc62e82de69d208e5d1670708588eb_address);
            EXPECT_EQ(block.transactions[2].amount, 0x3D3C2FC0CADDC00_u128);
            EXPECT_EQ(block.transactions[2].data, byte_string{});
            // Need to figure out the Signature Chain Stuff
        }
        // Transactions[3]
        {
            EXPECT_EQ(block.transactions[3].nonce, 886'729);
            EXPECT_EQ(block.transactions[3].gas_price, 20'000'000'000); // 20Gwei
            EXPECT_EQ(block.transactions[3].gas_limit, 90'000);
            EXPECT_EQ(*block.transactions[3].to, 0x31cca7cc41128aefcd0e35d9bdebadc75bf7ca27_address);
            EXPECT_EQ(block.transactions[3].amount, 0xDEE6C72F83B7184_u128);
            EXPECT_EQ(block.transactions[3].data, byte_string{});
            // Need to figure out the Signature Chain Stuff
        }
    }
    // Ommers (Should be nothing, Empty List)
    {
        EXPECT_EQ(block.ommers.size(), 0);
    }

}


// TEST(Rlp_Account, DecodeBlock2)
// {
//     byte_string block_encoding = read_block_asset(2730001);
//     byte_string_loc pos = 0;
//     Block block = decode_block(block_encoding,pos);

//     // Header
//     {
//         EXPECT_EQ(block.header.parent_hash, 0x18057c6cc208419928dbf4891af02d865f5d72f34f1880a3a3674b6a2585d8ec_bytes32);
//         EXPECT_EQ(block.header.ommers_hash, 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32);
//         EXPECT_EQ(block.header.beneficiary, 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address);
//         EXPECT_EQ(block.header.state_root, 0xbda8c4941b104eb8b2a698eef53e5bfa63f40b7497f2426a619623a82bdbfacd_bytes32);
//         // How to get the transaction root & receipt root & bloom of the block?
//         //EXPECT_EQ(block.hedaer.transaction_root, )
//         EXPECT_EQ(block.header.difficulty, 71133750415151);
//         EXPECT_EQ(block.header.number, 2730000);
//         EXPECT_EQ(block.header.gas_limit, 3'293'766);
//         EXPECT_EQ(block.header.gas_used, 84'000);
//         // How to get the uint64_t representation of timestamp?
//         EXPECT_EQ(block.header.extra_data, byte_string({0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69, 0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31}));
//     }
// }

