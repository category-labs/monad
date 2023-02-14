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

// glee: Not all data can easily be retrieved, though the data that has been
//       matches with our decoding. We believe this is fairly sufficient.
//       Alternatively, we could hook up our implementation to existing
//       repositories with encoders/decoders (i.e. silkworm) for testing.

TEST(Rlp_Block, DecodeBlock2730000)
{
    using namespace intx;

    byte_string block_encoding = read_block_asset(2730000);
    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding, pos);
    // Header
    EXPECT_EQ(block.header.parent_hash, 0x18057c6cc208419928dbf4891af02d865f5d72f34f1880a3a3674b6a2585d8ec_bytes32);
    EXPECT_EQ(block.header.ommers_hash, 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32);
    EXPECT_EQ(block.header.beneficiary, 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address);
    EXPECT_EQ(block.header.state_root, 0xbda8c4941b104eb8b2a698eef53e5bfa63f40b7497f2426a619623a82bdbfacd_bytes32);
    EXPECT_EQ(block.header.difficulty, 71133750415151);
    EXPECT_EQ(block.header.number, 2730000);
    EXPECT_EQ(block.header.gas_limit, 3293766);
    EXPECT_EQ(block.header.gas_used, 84000);
    EXPECT_EQ(block.header.timestamp, 1480625618);
    EXPECT_EQ(block.header.extra_data, byte_string({0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69, 0x6e, 0x65, 0x20, 0x2d, 0x20, 0x45, 0x55, 0x31}));
    EXPECT_EQ(block.header.nonce, byte_string_fixed<8UL>({0x5b, 0x75, 0xd1, 0x38, 0x22, 0xb5, 0xe1, 0xd4}));

    EXPECT_EQ(block.transactions[0].nonce, 1639528);
    EXPECT_EQ(block.transactions[0].gas_price, 25000000000);
    EXPECT_EQ(block.transactions[0].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[0].to, 0xBB474EdbC0C6ecF5c0455F8e6F90b8D46098e016_address);
    EXPECT_EQ(block.transactions[0].amount, 0x3dd59a7fca63400_u128);

    EXPECT_EQ(block.transactions[1].nonce, 886728);
    EXPECT_EQ(block.transactions[1].gas_price, 20000000000);
    EXPECT_EQ(block.transactions[1].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[1].to, 0x288E49EDb33A4B88860e8ce10A0407eaefd7dfdA_address);
    EXPECT_EQ(block.transactions[1].amount, 0x6ef6dd445b94970_u128);

    EXPECT_EQ(block.transactions[2].nonce, 1639529);
    EXPECT_EQ(block.transactions[2].gas_price, 25000000000);
    EXPECT_EQ(block.transactions[2].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[2].to, 0xA7895d323bFc62E82dE69D208E5d1670708588eB_address);
    EXPECT_EQ(block.transactions[2].amount, 0x3d3c2fc0caddc00_u128);

    EXPECT_EQ(block.transactions[3].nonce, 886729);
    EXPECT_EQ(block.transactions[3].gas_price, 20000000000);
    EXPECT_EQ(block.transactions[3].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[3].to, 0x31Cca7cc41128aeFCD0E35D9bdeBAdC75bF7CA27_address);
    EXPECT_EQ(block.transactions[3].amount, 0xdee6c72f83b7184_u128);

    EXPECT_EQ(block.transactions.size(), 4);

    EXPECT_EQ(block.ommers.size(), 0);
}

TEST(Rlp_Block, DecodeBlock2730001)
{
    using namespace intx;

    byte_string block_encoding = read_block_asset(2730001);
    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding, pos);
    // Header
    EXPECT_EQ(block.header.parent_hash, 0xfa0e5ba976931459e7aff38ba3800dfb4e75ba52b185cd41973d013b62c30b90_bytes32);
    EXPECT_EQ(block.header.ommers_hash, 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32);
    EXPECT_EQ(block.header.beneficiary, 0xEA674fdDe714fd979de3EdF0F56AA9716B898ec8_address);
    EXPECT_EQ(block.header.state_root, 0x7b674fc920d494b1186195fd9b81067c5311373e268972bc1fd3555768c5b119_bytes32);
    EXPECT_EQ(block.header.difficulty, 71064317416445);
    EXPECT_EQ(block.header.number, 2730001);
    EXPECT_EQ(block.header.gas_limit, 3296981);
    EXPECT_EQ(block.header.gas_used, 196834);
    EXPECT_EQ(block.header.timestamp, 1480625657);
    EXPECT_EQ(block.header.extra_data, byte_string({0x65, 0x74, 0x68, 0x65, 0x72, 0x6d, 0x69, 0x6e, 0x65, 0x20, 0x2d, 0x20, 0x55, 0x53, 0x31}));
    EXPECT_EQ(block.header.nonce, byte_string_fixed<8UL>({0x53, 0x29, 0x32, 0x80, 0x0d, 0x25, 0x45, 0xa0}));

    EXPECT_EQ(block.transactions[0].nonce, 1639530);
    EXPECT_EQ(block.transactions[0].gas_price, 25000000000);
    EXPECT_EQ(block.transactions[0].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[0].to, 0x92A4bc572595ed4851E0AbF8fF72a77bBa9323C0_address);
    EXPECT_EQ(block.transactions[0].amount, 0x3b7e74a7f3af400_u128);

    EXPECT_EQ(block.transactions[1].nonce, 21);
    EXPECT_EQ(block.transactions[1].gas_price, 20000000000);
    EXPECT_EQ(block.transactions[1].gas_limit, 300000);
    EXPECT_EQ(*block.transactions[1].to, 0x65C28345d499b59606cFe3d0ed580a1d2370C7C9_address);
    EXPECT_EQ(block.transactions[1].amount, 0x0_u128);

    EXPECT_EQ(block.transactions[2].nonce, 92940);
    EXPECT_EQ(block.transactions[2].gas_price, 20000000000);
    EXPECT_EQ(block.transactions[2].gas_limit, 39000);
    EXPECT_EQ(*block.transactions[2].to, 0xeDc53fB256c8F5cd6f91AF675BBb89bFC3732c57_address);
    EXPECT_EQ(block.transactions[2].amount, 0xe7f24b03527b860_u128);

    EXPECT_EQ(block.transactions[3].nonce, 886730);
    EXPECT_EQ(block.transactions[3].gas_price, 20000000000);
    EXPECT_EQ(block.transactions[3].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[3].to, 0x33BE3ADC19fD04a21bEd5d55DC1FD1F9Df5439E1_address);
    EXPECT_EQ(block.transactions[3].amount, 0xe282b737fa1986c_u128);

    EXPECT_EQ(block.transactions[4].nonce, 1639531);
    EXPECT_EQ(block.transactions[4].gas_price, 25000000000);
    EXPECT_EQ(block.transactions[4].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[4].to, 0x57a5809cb4ED2e40630f5A0F26273dc08A9a92cd_address);
    EXPECT_EQ(block.transactions[4].amount, 0x39473f637aa0800_u128);

    EXPECT_EQ(block.transactions[5].nonce, 1639532);
    EXPECT_EQ(block.transactions[5].gas_price, 25000000000);
    EXPECT_EQ(block.transactions[5].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[5].to, 0x009fAC3897c8Acbc0AE6e2a92Bc0755AA9E91DCc_address);
    EXPECT_EQ(block.transactions[5].amount, 0x3907052df885000_u128);

    EXPECT_EQ(block.transactions[6].nonce, 1639533);
    EXPECT_EQ(block.transactions[6].gas_price, 25000000000);
    EXPECT_EQ(block.transactions[6].gas_limit, 90000);
    EXPECT_EQ(*block.transactions[6].to, 0x54Ee2a8B5C61a45749E89471C75d45d3159D6947_address);
    EXPECT_EQ(block.transactions[6].amount, 0x38ebe0341834c00_u128);

    EXPECT_EQ(block.transactions.size(), 7);

    EXPECT_EQ(block.ommers.size(), 0);
}

TEST(Rlp_Block, DecodeBlock2730002)
{
    using namespace intx;

    byte_string block_encoding = read_block_asset(2730002);
    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding, pos);
    // Header
    EXPECT_EQ(block.header.parent_hash, 0x46d016199b63472c503b5d26b33f22a810d20f552085433177b4817c59327eba_bytes32);
    EXPECT_EQ(block.header.ommers_hash, 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32);
    EXPECT_EQ(block.header.beneficiary, 0x61C808D82A3Ac53231750daDc13c777b59310bD9_address);
    EXPECT_EQ(block.header.state_root, 0x0adde1fb82a1735191d30b109e92441a53a10edee0d2f4f63114f134f8db6e8c_bytes32);
    EXPECT_EQ(block.header.difficulty, 71029651597139);
    EXPECT_EQ(block.header.number, 2730002);
    EXPECT_EQ(block.header.gas_limit, 3294051);
    EXPECT_EQ(block.header.gas_used, 0);
    EXPECT_EQ(block.header.timestamp, 1480625678);
    EXPECT_EQ(block.header.extra_data, byte_string({0xe4, 0xb8, 0x83, 0xe5, 0xbd, 0xa9, 0xe7, 0xa5, 0x9e, 0xe4, 0xbb, 0x99, 0xe9, 0xb1, 0xbc}));
    EXPECT_EQ(block.header.nonce, byte_string_fixed<8UL>({0x75, 0xa7, 0x11, 0x00, 0x0c, 0x57, 0xaa, 0x39}));

    EXPECT_EQ(block.transactions.size(), 0);

    EXPECT_EQ(block.ommers.size(), 0);
}

TEST(Rlp_Block, DecodeBlock2730009)
{
    using namespace intx;

    byte_string block_encoding = read_block_asset(2730009);
    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding, pos);
    // Header
    EXPECT_EQ(block.header.parent_hash, 0x278677e93d6b23c260fbedeccbace563c1c8708c6a632bf0730a55c117c4cb78_bytes32);
    EXPECT_EQ(block.header.ommers_hash, 0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347_bytes32);
    EXPECT_EQ(block.header.beneficiary, 0x2a65Aca4D5fC5B5C859090a6c34d164135398226_address);
    EXPECT_EQ(block.header.state_root, 0x9be6e85fc6dcd2c9493aab527bc1eed17a2cbbefc6cae43db11a57f110ef3d7b_bytes32);
    EXPECT_EQ(block.header.difficulty, 71168718072168);
    EXPECT_EQ(block.header.number, 2730009);
    EXPECT_EQ(block.header.gas_limit, 3300000);
    EXPECT_EQ(block.header.gas_used, 0);
    EXPECT_EQ(block.header.timestamp, 1480625740);
    EXPECT_EQ(block.header.extra_data, byte_string({0x44, 0x77, 0x61, 0x72, 0x66, 0x50, 0x6f, 0x6f, 0x6c}));
    EXPECT_EQ(block.header.nonce, byte_string_fixed<8UL>({0x11, 0x1a, 0x14, 0xd8, 0x09, 0x1d, 0x06, 0xe8}));

    EXPECT_EQ(block.transactions.size(), 0);

    EXPECT_EQ(block.ommers.size(), 0);
}
