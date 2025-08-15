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

#include <category/core/assert.h>
#include <category/core/config.hpp>
#include <category/execution/ethereum/db/file_db.hpp>

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <ios>
#include <optional>
#include <sstream>
#include <string>
#include <string_view>
#include <thread>

MONAD_NAMESPACE_BEGIN

class FileDb::Impl
{
    std::filesystem::path const dir_;

public:
    explicit Impl(char const *const dir)
        : dir_{dir}
    {
        std::filesystem::create_directories(dir_);
        MONAD_ASSERT(std::filesystem::is_directory(dir_));
    }

    std::optional<std::string> get(char const *const key) const
    {
        auto const path = dir_ / key;
        std::ifstream in{path, std::ios::in | std::ios::binary};
        if (!in) {
            return std::nullopt;
        }
        std::string value;
        in.seekg(0, std::ios::end);
        auto const pos = in.tellg();
        MONAD_ASSERT(pos >= 0);
        value.resize(static_cast<size_t>(pos));
        in.seekg(0, std::ios::beg);
        in.read(value.data(), static_cast<std::streamsize>(value.size()));
        in.close();
        return value;
    }

    void upsert(char const *const key, std::string_view const value) const
    {
        auto const path = dir_ / key;
        std::stringstream temp_name;
        temp_name << '_' << key << '.' << std::this_thread::get_id();
        auto const temp_path = dir_ / temp_name.str();
        std::ofstream out{
            temp_path, std::ios::out | std::ios::trunc | std::ios::binary};
        MONAD_ASSERT(out);
        out.write(value.data(), static_cast<std::streamsize>(value.size()));
        out.close();
        std::filesystem::rename(temp_path, path);
    }

    bool remove(char const *const key) const
    {
        auto const path = dir_ / key;
        return std::filesystem::remove(path);
    }
};

FileDb::FileDb(FileDb &&) = default;

FileDb::FileDb(char const *const dir)
    : impl_{new Impl{dir}}
{
}

FileDb::~FileDb() = default;

std::optional<std::string> FileDb::get(char const *const key) const
{
    return impl_->get(key);
}

void FileDb::upsert(char const *const key, std::string_view const value) const
{
    impl_->upsert(key, value);
}

bool FileDb::remove(char const *const key) const
{
    return impl_->remove(key);
}

MONAD_NAMESPACE_END
