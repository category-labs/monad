// Copyright (C) 2025 Category Labs, Inc.
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

#include <category/vm/compiler/transactional_unordered_map.hpp>

#include <gtest/gtest.h>
#include <string>

using namespace monad::vm::compiler;

TEST(transactional_unordered_map, test_0)
{
    TransactionalUnorderedMap<int, int> map{};
    ASSERT_EQ(map.find(0), map.end());
}

TEST(transactional_unordered_map, test_1)
{
    TransactionalUnorderedMap<std::string, int> map{
        {std::string{"0"}, 0}, {std::string{"1"}, 1}};

    ASSERT_EQ(map.at("0"), 0);
    ASSERT_EQ(map.at("1"), 1);
    ASSERT_EQ(map.find("1")->second, 1);

    map.put("2", 2);
    ASSERT_EQ(map.at("2"), 2);

    ASSERT_TRUE(map.erase("1"));

    ASSERT_EQ(map.find("1"), map.end());

    ASSERT_FALSE(map.erase("1"));
}

TEST(transactional_unordered_map, test_2)
{
    TransactionalUnorderedMap<std::string, int> map{
        {std::string{"0"}, 0}, {std::string{"1"}, 1}};

    map.transaction();

    map.put("2", 2);
    ASSERT_EQ(map.at("2"), 2);

    map.revert();

    ASSERT_EQ(map.find("2"), map.end());

    map.transaction();

    map.put("2", 2);

    map.transaction();

    map.put("3", 3);

    map.commit();

    map.transaction();

    map.put("4", 4);

    ASSERT_EQ(map.at("0"), 0);
    ASSERT_EQ(map.at("1"), 1);
    ASSERT_EQ(map.at("2"), 2);
    ASSERT_EQ(map.at("3"), 3);
    ASSERT_EQ(map.at("4"), 4);

    ASSERT_TRUE(map.erase("3"));
    ASSERT_FALSE(map.contains("3"));

    map.revert();

    ASSERT_EQ(map.at("0"), 0);
    ASSERT_EQ(map.at("1"), 1);
    ASSERT_EQ(map.at("2"), 2);
    ASSERT_EQ(map.at("3"), 3);
    ASSERT_EQ(map.find("4"), map.end());

    ASSERT_TRUE(map.erase("0"));
    ASSERT_TRUE(map.erase("2"));
    ASSERT_FALSE(map.contains("0"));
    ASSERT_FALSE(map.contains("2"));

    map.revert();

    ASSERT_EQ(map.at("0"), 0);
    ASSERT_EQ(map.at("1"), 1);
    ASSERT_EQ(map.find("2"), map.end());
    ASSERT_EQ(map.find("3"), map.end());
    ASSERT_EQ(map.find("4"), map.end());
}
