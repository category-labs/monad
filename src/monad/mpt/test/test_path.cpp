#include <gtest/gtest.h>
#include <iterator>
#include <monad/mpt/path.hpp>
#include <algorithm>
#include <iostream>

using namespace monad::mpt;

TEST(Path, Sanity)
{
    auto const& first_path = Path(monad::byte_string({0x01, 0x23, 0x45, 0x67}), Path::FromRawBytes{});

    // Check that the path was populated correctly
    EXPECT_EQ(first_path.size(), 8);
    EXPECT_EQ(first_path, Path({0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07}));

    // Check that empty path works
    auto const empty_path = Path(monad::byte_string{}, Path::FromRawBytes{});
    EXPECT_TRUE(empty_path.empty());
    EXPECT_EQ(empty_path.size(), 0);
    EXPECT_NE(empty_path, Path({0x00}));
}

TEST(Path, Iterator)
{
    auto first_path = Path(monad::byte_string({0x01, 0x23, 0x45, 0x67}), Path::FromRawBytes{});

    auto second_path = Path(first_path.begin(), first_path.end());

    EXPECT_EQ(first_path, second_path);

    auto third_path = Path(std::next(first_path.begin(), 2), first_path.end());

    EXPECT_EQ(third_path, Path({0x02, 0x03, 0x04, 0x05, 0x06, 0x07}));
}

TEST(Path, CommonPrefix)
{
    auto const first_path = Path(monad::byte_string({0x01, 0x23, 0x45, 0x67}), Path::FromRawBytes{});
    auto const empty_path = Path(monad::byte_string{}, Path::FromRawBytes{});

    // Verify that the common prefixes are expected
    EXPECT_EQ(first_path.common_prefix_size(empty_path), 0);
    EXPECT_EQ(first_path.common_prefix_size(first_path), first_path.size());

    // Create second path with non-zero common prefix
    auto second_path = Path(monad::byte_string({0x01, 0x23, 0x67}), Path::FromRawBytes{});

    EXPECT_EQ(second_path, Path({0x00, 0x01, 0x02, 0x03, 0x06, 0x07}));

    // Verify that common prefix is expected
    EXPECT_EQ(first_path.common_prefix_size(second_path), 4);
}

TEST(Path, PrefixModification)
{
    auto first_path = Path(monad::byte_string({0x01, 0x23, 0x45, 0x67}), Path::FromRawBytes{});
    auto first_path_view = PathView(first_path);
    auto const empty_path = Path(monad::byte_string{}, Path::FromRawBytes{});

    // Remove prefix and check sizes for both paths
    auto suffix = first_path_view.suffix(first_path_view.size() - 4);

    // Original path should not have changed
    EXPECT_EQ(first_path, Path({0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07}));
    EXPECT_EQ(first_path.size(), 8);

    // The view should have though
    EXPECT_EQ(suffix, Path({0x04, 0x05, 0x06, 0x07}));
    EXPECT_EQ(suffix.size(), 4);

    auto second_path = Path(monad::byte_string({0x01, 0x23, 0x67}), Path::FromRawBytes{});
    auto second_path_view = PathView(second_path);
    suffix = second_path_view.suffix(second_path_view.size() - 4);

    EXPECT_FALSE(suffix.empty());
    EXPECT_EQ(suffix.size(), 2);
    EXPECT_EQ(suffix, Path({0x06, 0x07}));

    auto third_path = Path(monad::byte_string({0x45, 0x67, 0x89}), Path::FromRawBytes{});
    auto third_path_view = PathView(third_path);

    auto const original_expected_value =
        Path({0x04, 0x05, 0x06, 0x07, 0x08, 0x09});
    EXPECT_EQ(third_path_view, original_expected_value);

    auto prefix = third_path_view.prefix(4);
    EXPECT_EQ(prefix, Path({0x04, 0x05, 0x06, 0x07}));

    suffix = prefix.suffix(prefix.size() - 2);
    EXPECT_EQ(suffix, Path({0x06, 0x07}));

    suffix = suffix.suffix(suffix.size() - 2);
    EXPECT_TRUE(suffix.empty());
    EXPECT_EQ(suffix.size(), 0);
    EXPECT_EQ(suffix, Path{});

    // Original path should not have changed
    EXPECT_EQ(third_path.size(), 6);
    EXPECT_EQ(third_path, original_expected_value);
}

TEST(Path, CompactEncoding)
{
    auto path = Path{Path({0x01, 0x02, 0x03, 0x04, 0x05})};

    EXPECT_EQ(path.compact_encoding<EncodeExtension>(), monad::byte_string({0x11, 0x23, 0x45}));
    EXPECT_EQ(path.compact_encoding<EncodeLeaf>(), monad::byte_string({0x31, 0x23, 0x45}));

    path = Path{Path({0x00, 0x01, 0x02, 0x03, 0x04, 0x05})};

    EXPECT_EQ(path.compact_encoding<EncodeExtension>(), monad::byte_string({0x00, 0x01, 0x23, 0x45}));
    EXPECT_EQ(path.compact_encoding<EncodeLeaf>(), monad::byte_string({0x20, 0x01, 0x23, 0x45}));

    path = Path{Path({0x00, 0x0f, 0x01, 0x0c, 0x0b, 0x08})};

    EXPECT_EQ(path.compact_encoding<EncodeExtension>(), monad::byte_string({0x00, 0x0f, 0x1c, 0xb8}));
    EXPECT_EQ(path.compact_encoding<EncodeLeaf>(), monad::byte_string({0x20, 0x0f, 0x1c, 0xb8}));

    path = Path{Path({0x0f, 0x01, 0x0c, 0x0b, 0x08})};
    EXPECT_EQ(path.compact_encoding<EncodeExtension>(), monad::byte_string({0x1f, 0x1c, 0xb8}));
    EXPECT_EQ(path.compact_encoding<EncodeLeaf>(), monad::byte_string({0x3f, 0x1c, 0xb8}));
}

TEST(Path, ConstructFromCompactEncoding)
{
    auto path = Path(monad::byte_string({0x31, 0x23, 0x45}), Path::FromCompactEncoding{});

    EXPECT_EQ(path, Path({0x01, 0x02, 0x03, 0x04, 0x05}));

    path = Path(monad::byte_string({0x20, 0x01, 0x23, 0x45}), Path::FromCompactEncoding{});

    EXPECT_EQ(path, Path({0x00, 0x01, 0x02, 0x03, 0x04, 0x05}));

    path = Path(monad::byte_string({0x20, 0x0f, 0x1c, 0xb8}), Path::FromCompactEncoding{});

    EXPECT_EQ(path, Path({0x00, 0x0f, 0x01, 0x0c, 0x0b, 0x08}));

    path = Path(monad::byte_string({0x3f, 0x1c, 0xb8}), Path::FromCompactEncoding{});

    EXPECT_EQ(path, Path({0x0f, 0x01, 0x0c, 0x0b, 0x08}));
}
