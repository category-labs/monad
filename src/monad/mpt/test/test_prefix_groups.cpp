#include <gtest/gtest.h>
#include <monad/mpt/prefix_groups.hpp>

using namespace monad::mpt;

TEST(PrefixGroups, Sanity)
{
    PrefixGroups groups;

    EXPECT_TRUE(groups.empty());

    // Add prefix group with 0 length
    groups.add_branch(0, Nibble{0xf});

    EXPECT_FALSE(groups.empty());

    auto group = groups.get_current_group();

    // Verify that it got added correctly
    EXPECT_EQ(group.length, 0);
    EXPECT_EQ(group.branches, Branches{Nibble{0xf}});

    // Add prefix group with length 20
    groups.add_branch(20, Nibble{0x1});

    group = groups.get_current_group();
    
    // Again, verify that it got added correctly
    EXPECT_EQ(group.length, 20);
    EXPECT_EQ(group.branches, Branches{Nibble{0x1}});

    // Add another branch to the same prefix
    groups.add_branch(20, Nibble{0xf});

    group = groups.get_current_group();

    // Verify that there are now two branches at prefix with length 20
    auto expected_branches = Branches{Nibble{0x1}};
    expected_branches.add_branch(Nibble{0xf});

    EXPECT_EQ(group.length, 20);
    EXPECT_EQ(group.branches, expected_branches);

    // Pop prefix group with length 20 off
    groups.pop_current_group();
    
    EXPECT_FALSE(groups.empty());

    group = groups.get_current_group();

    // Verify that what we get back is the prefix group with length 0
    EXPECT_EQ(group.length, 0);
    EXPECT_EQ(group.branches, Branches{Nibble{0xf}});

    // Now pop it off
    groups.pop_current_group();

    EXPECT_TRUE(groups.empty());
}
