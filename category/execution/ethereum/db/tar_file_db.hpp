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

#pragma once

#include <category/core/config.hpp>

#include <filesystem>
#include <memory>
#include <optional>
#include <string>

MONAD_NAMESPACE_BEGIN

// Block store backed by plain .tar archives. Accepts either:
//   * a single .tar file (entries keyed by decimal block number); or
//   * a directory containing one <N>M.tar per million-block bucket.
// In the directory form, only one bucket is held open at a time.
class TarFileDb final
{
    class Impl;

    std::unique_ptr<Impl> impl_;

public:
    TarFileDb() = delete;
    TarFileDb(TarFileDb const &) = delete;
    TarFileDb(TarFileDb &&) noexcept;
    explicit TarFileDb(std::filesystem::path const &);
    ~TarFileDb();

    std::optional<std::string> get(char const *key) const;

    static bool looks_like_tar_backed(std::filesystem::path const &);
};

MONAD_NAMESPACE_END
