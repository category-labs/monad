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

#include <memory>
#include <optional>
#include <string>
#include <string_view>

MONAD_NAMESPACE_BEGIN

class FileDb final
{
    class Impl;

    std::unique_ptr<Impl> impl_;

public:
    FileDb() = delete;
    FileDb(FileDb const &) = delete;
    FileDb(FileDb &&);
    explicit FileDb(char const *dir);
    ~FileDb();

    std::optional<std::string> get(char const *key) const;

    void upsert(char const *key, std::string_view value) const;
    bool remove(char const *key) const;
};

MONAD_NAMESPACE_END
