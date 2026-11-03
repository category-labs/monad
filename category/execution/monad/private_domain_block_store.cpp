// Copyright (C) 2025-26 Category Labs, Inc.
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

#include <category/execution/monad/private_domain_block_store.hpp>

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/execution/monad/core/domain_block.hpp>
#include <category/execution/monad/core/rlp/domain_block_rlp.hpp>

#include <algorithm>
#include <cerrno>
#include <charconv>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iterator>
#include <optional>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>
#include <vector>

#include <fcntl.h>
#include <unistd.h>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

namespace fs = std::filesystem;

std::optional<uint64_t> parse_number(std::string_view const name)
{
    uint64_t number{};
    auto const [end, ec] =
        std::from_chars(name.data(), name.data() + name.size(), number);
    if (ec != std::errc{} || end != name.data() + name.size()) {
        return std::nullopt;
    }
    return number;
}

// The numbers naming entries of `dir`, largest first. Other names, such as
// temporary files, are skipped.
std::vector<uint64_t> numbered_entries(fs::path const &dir)
{
    std::vector<uint64_t> numbers;
    for (auto const &entry : fs::directory_iterator{dir}) {
        if (auto const number =
                parse_number(entry.path().filename().string())) {
            numbers.push_back(*number);
        }
    }
    std::ranges::sort(numbers, std::greater{});
    return numbers;
}

void fsync_path(fs::path const &path, int const flags)
{
    int const fd = ::open(path.c_str(), flags | O_CLOEXEC);
    MONAD_ASSERT_PRINTF(
        fd != -1, "open %s failed: %s", path.c_str(), std::strerror(errno));
    MONAD_ASSERT_PRINTF(
        ::fsync(fd) == 0,
        "fsync %s failed: %s",
        path.c_str(),
        std::strerror(errno));
    ::close(fd);
}

void write_file(fs::path const &path, byte_string_view data)
{
    auto const temporary = fs::path{path.string() + ".tmp"};
    int const fd = ::open(
        temporary.c_str(), O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0644);
    MONAD_ASSERT_PRINTF(
        fd != -1,
        "open %s failed: %s",
        temporary.c_str(),
        std::strerror(errno));
    while (!data.empty()) {
        auto const written = ::write(fd, data.data(), data.size());
        MONAD_ASSERT_PRINTF(
            written > 0,
            "write %s failed: %s",
            temporary.c_str(),
            std::strerror(errno));
        data.remove_prefix(static_cast<size_t>(written));
    }
    MONAD_ASSERT_PRINTF(
        ::fsync(fd) == 0,
        "fsync %s failed: %s",
        temporary.c_str(),
        std::strerror(errno));
    ::close(fd);
    fs::rename(temporary, path);
    fsync_path(path.parent_path(), O_RDONLY | O_DIRECTORY);
}

std::optional<byte_string> read_file(fs::path const &path)
{
    std::ifstream in{path, std::ios::binary};
    if (!in) {
        return std::nullopt;
    }
    std::string const contents{
        std::istreambuf_iterator<char>{in}, std::istreambuf_iterator<char>{}};
    MONAD_ASSERT_PRINTF(!in.bad(), "read %s failed", path.c_str());
    return byte_string{contents.begin(), contents.end()};
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

DomainBlockStore::DomainBlockStore(
    fs::path dir, uint64_t const blocks_per_directory)
    : dir_{std::move(dir)}
    , blocks_per_directory_{blocks_per_directory}
{
    MONAD_ASSERT(blocks_per_directory_ > 0);
    fs::create_directories(dir_ / "blocks");

    if (auto const cursor = read_file(dir_ / "cursor")) {
        std::string_view const text{
            reinterpret_cast<char const *>(cursor->data()), cursor->size()};
        l1_cursor_ = parse_number(text);
        MONAD_ASSERT_PRINTF(
            l1_cursor_.has_value(), "corrupt cursor in %s", dir_.c_str());
    }

    // The tip is the largest block of the largest directory that holds one:
    // a crash between creating a directory and writing its first block
    // leaves it empty.
    for (auto const directory : numbered_entries(dir_ / "blocks")) {
        auto const numbers =
            numbered_entries(dir_ / "blocks" / std::to_string(directory));
        if (!numbers.empty()) {
            tip_ = get(numbers.front());
            MONAD_ASSERT(tip_.has_value());
            break;
        }
    }
}

fs::path DomainBlockStore::block_path(uint64_t const number) const
{
    return dir_ / "blocks" / std::to_string(number / blocks_per_directory_) /
           std::to_string(number);
}

std::optional<DomainBlock> DomainBlockStore::get(uint64_t const number) const
{
    auto const path = block_path(number);
    auto const encoded = read_file(path);
    if (!encoded.has_value()) {
        return std::nullopt;
    }
    byte_string_view view{*encoded};
    auto block = rlp::decode_domain_block(view);
    MONAD_ASSERT_PRINTF(
        block.has_value() && view.empty() &&
            block.value().header.number == number,
        "corrupt domain block %s",
        path.c_str());
    return std::move(block).value();
}

void DomainBlockStore::append(DomainBlock const &block)
{
    MONAD_ASSERT_PRINTF(
        block.header.number == (tip_ ? tip_->header.number + 1 : 0),
        "domain block %lu does not follow the store's tip",
        block.header.number);
    auto const path = block_path(block.header.number);
    if (!fs::exists(path.parent_path())) {
        fs::create_directory(path.parent_path());
        fsync_path(path.parent_path().parent_path(), O_RDONLY | O_DIRECTORY);
    }
    write_file(path, rlp::encode_domain_block(block));
    tip_ = block;
}

void DomainBlockStore::set_l1_cursor(uint64_t const l1_block_number)
{
    auto const text = std::to_string(l1_block_number);
    write_file(dir_ / "cursor", byte_string{text.begin(), text.end()});
    l1_cursor_ = l1_block_number;
}

MONAD_NAMESPACE_END
