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

    std::ifstream input(path.c_str());
    byte_string output;
    char buf;

    // glee: there probably is a more correct way to do this...
    if (input)
    {
        while (input.read(&buf, 1))
        {
            output += buf;
        }
    }
    return output;
}

TEST(Rlp_Account, DecodeBlock)
{
    byte_string block_encoding = read_block_asset(2730000);
    std::cerr << block_encoding.length() << std::endl;
    for(int i=0;i<static_cast<int>(block_encoding.length());++i){
        std::cout << block_encoding[i];
    }
    std::cout << std::endl;

    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding,pos);

    EXPECT_EQ(block.header.parent_hash, 0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32);
}

