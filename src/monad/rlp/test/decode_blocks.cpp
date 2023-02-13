#include <monad/core/account.hpp>
#include <monad/rlp/encode_helpers.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/core/block.hpp>

#include <gtest/gtest.h>
#include <string>
#include <fstream>
#include <iostream>

using namespace monad;
using namespace monad::rlp;

byte_string read_from_file(std::string filename){
    byte_string bs;
    std::ifstream ifile(filename);
    unsigned char uc;
    while(ifile >> uc){
        bs+=uc;
    }
    return bs;
}

TEST(rlp_block, DecodeBlock){
    byte_string block_encoding = read_from_file("assets/block_encodings/2730000");
    std::cerr << block_encoding.length() << std::endl;
    for(int i=0;i<static_cast<int>(block_encoding.length());++i){
        std::cout << block_encoding[i];
    }
    std::cout << std::endl;

    byte_string_loc pos = 0;
    Block block = decode_block(block_encoding,pos);

    EXPECT_EQ(block.header.parent_hash, 0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32);
}