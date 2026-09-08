// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

#include <category/core/assert.h>
#include <category/core/blake3.hpp>
#include <category/core/hex.hpp>
#include <category/execution/runloop/file_io.hpp>

#include <gtest/gtest.h>

#include <cstdlib>
#include <filesystem>
#include <fstream>

namespace
{
    struct TempDir
    {
        std::filesystem::path path;

        TempDir()
        {
            auto const tmpl = std::filesystem::temp_directory_path() /
                              "monad_file_io_test_XXXXXX";
            auto mutable_tmpl = tmpl.string();
            char *const result = ::mkdtemp(mutable_tmpl.data());
            MONAD_ASSERT(result != nullptr);
            path = result;
        }

        TempDir(TempDir const &) = delete;
        TempDir &operator=(TempDir const &) = delete;

        ~TempDir()
        {
            std::error_code ec;
            std::filesystem::remove_all(path, ec);
        }
    };
}

TEST(FileIo, ReadsContentAddressedAlias)
{
    using namespace monad;

    TempDir const dir;
    byte_string const data{0x01, 0x23, 0x45, 0x67, 0x89};
    auto const content_id = to_bytes(blake3(data));
    auto alias_id = content_id;
    alias_id.bytes[0] ^= 0xff;

    auto const content_path = dir.path / to_hex(content_id);
    std::ofstream output{content_path, std::ios::binary};
    output.write(
        reinterpret_cast<char const *>(data.data()),
        static_cast<std::streamsize>(data.size()));
    output.close();

    std::filesystem::create_symlink(
        content_path, dir.path / to_hex(alias_id));

    EXPECT_EQ(read_file(alias_id, dir.path), data);
}
