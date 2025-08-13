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
#include <category/core/cmemory.hpp>
#include <category/core/unordered_map.hpp>

#include <CLI/CLI.hpp>

#include <algorithm>
// #include <asm-generic/int-ll64.h>  NOLINT
#include <bit>
#include <cassert>
#include <cerrno>
#include <chrono>
#include <compare>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <exception>
#include <filesystem>
#include <format>
#include <fstream>
#include <functional>
#include <future>
#include <iostream>
#include <map>
#include <span>
#include <stdlib.h>
#include <string>
#include <system_error>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#if __has_include(<snappy.h>)
    #define MONAD_GETH_FREEZER_DB_HAVE_SNAPPY_H 1
    #include <snappy.h>
#else
    #define MONAD_GETH_FREEZER_DB_HAVE_SNAPPY_H 0
#endif

using file_offset_t = __u64;
template <class Key, class T>
using unordered_dense_map = monad::unordered_dense_map<Key, T>;
template <class Key>
using unordered_dense_set = monad::unordered_dense_set<Key>;

/* Firstly, https://superlunar.com/post/geth-freezer-files-block-data-done-fast
is extremely useful for the geth freezer db internal format.

Biggest entry for each table up to block 13,786,834:

- bodies: 1,467,191 bytes
    1. List of Transactions
        List of nine items (legacy transaction record format):
          1. One or two byte value (nonce of sender account)
          2. Five byte value (wei per gas)
          3. Two or three byte value (gas limit)
          4. Twenty byte value (to address)
          5. Either an empty list or a seven or eight byte value (wei amount)
          6. Either an empty list or a possibly quite large value (2404 bytes)
(contract invocation input data)
          7. A one byte value (V signature)
          8. A thirty-two byte value (R signature)
          9. A thirty-two byte value (S signature)
        OR value (new format transactions)
    2. List of Uncles
- diffs: 11 bytes
- hashes: 32 bytes
    - Probably just keccak256 of that block
- headers: 556 bytes
    - ETH header structure for that block
- receipts: 1,149,775 bytes

To calculate the sender address from a legacy transaction, one uses the
Homestead signer for legacy transactions. You will need the message
which was signed, which is the RLP encoding of the transaction but with
v replaced with the chain id and r and s all bits zero. The hash of that
is the input to the signing process, and you want to retrieve the public
key used. The sender's address is the last twenty bytes of that public key.

Other interesting data is top five accounts receiving most transactions:

1. https://etherscan.io/address/0xdac17f958d2ee523a2206206994597c13d831ec7
(Bitfinex: Deployer Contract)
2. https://etherscan.io/address/0x00000000006c3852cbef3e08e8df289169ede581
(OpenSea: Deployer Contract)
3. https://etherscan.io/address/0xef1c6e67703c7bd7107eed8303fbe6ec2554bf6b
(unknown contract)
4. https://etherscan.io/address/0xa0b86991c6218b36c1d19d4a2e9eb0ce3606eb48
(Circle: Deployer Contract)
5. https://etherscan.io/address/0x7a250d5630b4cf539739df2c5dacb4c659f2488d
(Uniswap: Deployer Contract)

Also:

- Under 2% of all accounts are recipients of 65% of all transactions.
- Under 5% of all accounts are recipients of 75% of all transactions.
- Around one third of all accounts are recipients of 90% of all transactions.
- Around two thirds of all accounts are recipients of 95% of all transactions.

- The regression line for this is (6 ^ (6 * ratio)) / (6 ^ 6)
*/
class FreezerDB
{
    static constexpr size_t DATA_CHUNK_SIZE_ = 2ULL * 1024 * 1024 * 1024;

    struct idxfile_entry_
    {
        std::byte rawbytes[6];

        uint16_t file_number() const noexcept
        {
            if constexpr (std::endian::native != std::endian::big) {
                return uint16_t(uint16_t(rawbytes[0]) << 8) |
                       uint16_t(uint16_t(rawbytes[1]) << 0);
            }
            return uint16_t(uint16_t(rawbytes[1]) << 8) |
                   uint16_t(uint16_t(rawbytes[0]) << 0);
        }

        uint32_t file_offset() const noexcept
        {
            if constexpr (std::endian::native != std::endian::big) {
                return (uint32_t(rawbytes[5]) << 0) |
                       (uint32_t(rawbytes[4]) << 8) |
                       (uint32_t(rawbytes[3]) << 16) |
                       (uint32_t(rawbytes[2]) << 24);
            }
            return (uint32_t(rawbytes[5]) << 24) |
                   (uint32_t(rawbytes[4]) << 16) |
                   (uint32_t(rawbytes[3]) << 8) | (uint32_t(rawbytes[2]) << 0);
        }
    };

    static_assert(sizeof(idxfile_entry_) == 6);
    static_assert(std::is_trivially_copyable_v<idxfile_entry_>);

public:
    class table
    {
        std::filesystem::path const name_;
        bool const is_compressed_;
        std::span<idxfile_entry_ const> index_;
        std::span<std::byte const> data_reservation_;
        std::vector<std::span<std::byte const>> data_;

    public:
        table(std::filesystem::path indexpath, file_offset_t databytes)
            : name_(indexpath.filename().replace_extension())
            , is_compressed_(indexpath.filename().extension() == ".cidx")
        {
            auto do_mmap = [](void *addr, std::filesystem::path const &p)
                -> std::span<std::byte const> {
                int const fd = ::open(p.c_str(), O_RDONLY);
                if (-1 == fd) {
                    throw std::system_error(errno, std::system_category());
                }
                struct stat s;
                memset(&s, 0, sizeof(s));
                if (-1 == ::fstat(fd, &s)) {
                    throw std::system_error(errno, std::system_category());
                }
                auto *m = ::mmap(
                    (void *)addr,
                    size_t(s.st_size),
                    PROT_READ,
                    MAP_SHARED,
                    fd,
                    0);
                if (MAP_FAILED == m) {
                    throw std::system_error(errno, std::system_category());
                }
                ::close(fd);
                return {(const std::byte *)m, size_t(s.st_size)};
            };
            {
                auto r = do_mmap(nullptr, indexpath);
                index_ = {
                    (idxfile_entry_ const *)r.data(),
                    r.size() / sizeof(idxfile_entry_)};
            }
            auto *r = (std::byte *)::mmap(
                nullptr,
                databytes,
                PROT_NONE,
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE,
                -1,
                0);
            if (MAP_FAILED == r) {
                throw std::system_error(errno, std::system_category());
            }
            data_reservation_ = {r, databytes};
            size_t const segments =
                (databytes + DATA_CHUNK_SIZE_ - 1) / DATA_CHUNK_SIZE_;
            data_.reserve(segments);
            auto const newextension = (indexpath.extension() == ".cidx")
                                          ? std::string(".cdat")
                                          : std::string(".rdat");
            for (size_t idx = 0; idx < segments; idx++) {
                auto segment(indexpath);
                segment.replace_extension(
                    std::format(".{:04}{}", idx, newextension));
                data_.push_back(do_mmap(r + idx * DATA_CHUNK_SIZE_, segment));
            }
        }

        ~table()
        {
            data_.clear();
            ::munmap(
                (void *)data_reservation_.data(),
                data_reservation_.size_bytes());
            ::munmap((void *)index_.data(), index_.size_bytes());
        }

        std::filesystem::path const &name() const noexcept
        {
            return name_;
        }

        bool is_compressed() const noexcept
        {
            return is_compressed_;
        }

        file_offset_t bytes_consumed() const noexcept
        {
            return data_reservation_.size_bytes();
        }

        size_t size() const noexcept
        {
            /* Indices look to be appended in preparation for the next item
            to be added, so the last index won't point at anything useful
            */
            return index_.size() - 1;
        }

        std::span<std::byte const> raw_contents(size_t idx) const noexcept
        {
            if (idx >= index_.size()) {
                return {};
            }
            auto const &idx1_ = index_[idx];
            auto const segment = data_[idx1_.file_number()];
            if (idx + 1 >= index_.size()) {
                return segment.subspan(idx1_.file_offset());
            }
            auto const &idx2_ = index_[idx + 1];
            if (idx2_.file_number() != idx1_.file_number()) {
                /* The data is actually at the front of the next
                segment, not at where the index points
                */
                return data_[idx2_.file_number()].subspan(
                    0, idx2_.file_offset());
            }
            return segment.subspan(
                idx1_.file_offset(), idx2_.file_offset() - idx1_.file_offset());
        }

        size_t uncompressed_contents_length(size_t idx) const noexcept
        {
            auto const raw = raw_contents(idx);
            MONAD_DEBUG_ASSERT(raw.size() > 0);
            if (!is_compressed()) {
                return raw.size();
            }
#if MONAD_GETH_FREEZER_DB_HAVE_SNAPPY_H
            size_t result = 0;
            if (snappy::GetUncompressedLength(
                    (char const *)raw.data(), raw.size(), &result)) {
                return result;
            }
#endif
            return size_t(-1);
        }

        std::span<std::byte const>
        contents(std::span<std::byte> tofill, size_t idx) const
        {
            (void)tofill;
            auto const raw = raw_contents(idx);
            MONAD_DEBUG_ASSERT(raw.size() > 0);
            if (!is_compressed()) {
                return raw;
            }
#if MONAD_GETH_FREEZER_DB_HAVE_SNAPPY_H
            size_t result = 0;
            if (!snappy::GetUncompressedLength(
                    (char const *)raw.data(), raw.size(), &result)) {
                abort();
            }
            if (result > tofill.size()) {
                abort();
            }
            if (!snappy::RawUncompress(
                    (char const *)raw.data(),
                    raw.size(),
                    (char *)tofill.data())) {
                abort();
            }
            return tofill.subspan(0, result);
#endif
            return {};
        }
    };

    class rlp_item
    {
        std::byte const v_[2];

        rlp_item() = delete;
        rlp_item(rlp_item const &) = delete;
        ~rlp_item() = delete;

        template <size_t base_rlp>
        constexpr void get_long_string_length_(
            size_t &lengthbytes, uint64_t &stringlengthbytes) const noexcept
        {
            stringlengthbytes = 0;
            lengthbytes = size_t(v_[0]) - (base_rlp - 1);
            for (size_t n = 0; n < lengthbytes; n++) {
                stringlengthbytes <<= 8;
                stringlengthbytes |= uint8_t(v_[1 + n]);
            }
        }

    public:
        // Returns the next rlp_item
        constexpr rlp_item const *next(std::byte const *maximum) const noexcept
        {
            auto calculate = [this] {
                if (v_[0] >= std::byte(0x00) && v_[0] < std::byte(0x80)) {
                    return (rlp_item const *)((uintptr_t)this + 1);
                }
                if (v_[0] >= std::byte(0x80) && v_[0] < std::byte(0xb8)) {
                    return (rlp_item const *)((uintptr_t)this + 1 +
                                              size_t(v_[0]) - 0x80);
                }
                if (v_[0] >= std::byte(0xb8) && v_[0] < std::byte(0xc0)) {
                    size_t lenbytes;
                    uint64_t length;
                    get_long_string_length_<0xb8>(lenbytes, length);
                    return (rlp_item const *)((uintptr_t)this + 1 + lenbytes +
                                              length);
                }
                if (v_[0] >= std::byte(0xc0) && v_[0] < std::byte(0xf8)) {
                    return (rlp_item const *)((uintptr_t)this + 1 +
                                              size_t(v_[0]) - 0xc0);
                }
                if (v_[0] >= std::byte(0xf8) && v_[0] <= std::byte(0xff)) {
                    size_t lenbytes;
                    uint64_t length;
                    get_long_string_length_<0xf8>(lenbytes, length);
                    return (rlp_item const *)((uintptr_t)this + 1 + lenbytes +
                                              length);
                }
                __builtin_unreachable();
            };
            auto const *ret = calculate();
            if ((std::byte const *)ret >= maximum) {
                return nullptr;
            }
            return ret;
        }

        // The value of this rlp_item, if it has a value
        constexpr std::span<std::byte const> value() const noexcept
        {
            if (v_[0] >= std::byte(0x00) && v_[0] < std::byte(0x80)) {
                return {v_, 1};
            }
            if (v_[0] >= std::byte(0x80) && v_[0] < std::byte(0xb8)) {
                return {v_ + 1, size_t(v_[0]) - 0x80};
            }
            if (v_[0] >= std::byte(0xb8) && v_[0] < std::byte(0xc0)) {
                size_t lenbytes;
                uint64_t length;
                get_long_string_length_<0xb8>(lenbytes, length);
                return {v_ + 1 + lenbytes, length};
            }
            return {}; // I am a list
        }

        // The first item in the list and the list size in bytes, if this item
        // refers to a list
        constexpr std::pair<rlp_item const *, size_t> list() const noexcept
        {
            if (v_[0] >= std::byte(0xc0) && v_[0] < std::byte(0xf8)) {
                return {
                    (rlp_item const *)((uintptr_t)this + 1),
                    size_t(v_[0]) - 0xc0};
            }
            if (v_[0] >= std::byte(0xf8) && v_[0] <= std::byte(0xff)) {
                size_t lenbytes;
                uint64_t length;
                get_long_string_length_<0xf8>(lenbytes, length);
                return {
                    (rlp_item const *)((uintptr_t)this + 1 + lenbytes), length};
            }
            return {}; // I am a value
        }
    };

    static_assert(alignof(rlp_item) == 1);
    static_assert(std::is_trivially_copyable_v<rlp_item>);

private:
    std::vector<table> tables_;

public:
    explicit FreezerDB(std::filesystem::path dbpath)
    {
        dbpath /= "chain";
        std::map<std::filesystem::path, file_offset_t> indices;
        for (auto const &entry : std::filesystem::directory_iterator(dbpath)) {
            auto path = entry.path();
            auto const ext = path.extension();
            if (ext == ".cdat") {
                path.replace_extension("").replace_extension(".cidx");
                indices[path] += DATA_CHUNK_SIZE_;
            }
            else if (ext == ".rdat") {
                path.replace_extension("").replace_extension(".ridx");
                indices[path] += DATA_CHUNK_SIZE_;
            }
        }
        tables_.reserve(indices.size());
        for (auto &i : indices) {
            tables_.emplace_back(i.first, i.second);
        }
    }

    std::span<table const> tables() const noexcept
    {
        return tables_;
    }
};

struct eth_address
{
    std::byte v[20];

    constexpr bool operator==(eth_address const &o) const noexcept
    {
        return this->operator<=>(o) == std::strong_ordering::equal;
    }

    constexpr std::strong_ordering
    operator<=>(eth_address const &o) const noexcept
    {
        auto r = monad::cmemcmp(v, o.v, 20);
        if (r < 0) {
            return std::strong_ordering::less;
        }
        if (r > 0) {
            return std::strong_ordering::greater;
        }
        return std::strong_ordering::equal;
    }
};

template <>
struct std::hash<eth_address>
{
    size_t operator()(eth_address const &v) const noexcept
    {
        size_t ret;
        memcpy(&ret, v.v, sizeof(ret));
        return ret;
    }
};

uint32_t calculate_histogram_by_transaction(
    std::filesystem::path const &outpath, FreezerDB::table const &bodies_table,
    size_t blockno_begin, size_t blockno_end)
{
    unordered_dense_map<eth_address, uint32_t> map;
    std::vector<uint32_t> transactions_per_block(blockno_end - blockno_begin);
    std::byte buffer[4 * 1024 * 1024];
    uint32_t largest_count = 0;
    uint32_t total_transactions = 0;
    uint32_t unparsed_transactions = 0;
    for (size_t idx = blockno_begin; idx < blockno_end; idx++) {
        auto const contents = bodies_table.contents(buffer, idx);
        auto const bodies_list =
            ((FreezerDB::rlp_item const *)contents.data())->list();
        auto const txns_list = bodies_list.first->list();
        auto const *txns_list_end =
            (std::byte const *)txns_list.first + txns_list.second;
        unordered_dense_set<eth_address> seen;
        for (auto const *txn = txns_list.first; txn != nullptr;
             txn = txn->next(txns_list_end)) {
            auto const txn_is_value = txn->value();
            std::pair<FreezerDB::rlp_item const *, size_t> txn_list{nullptr, 0};
            if (!txn_is_value.empty()) {
                // If txn is a value, could be EIP-1559 or EIP-2930
                if (txn_is_value.size() > 1 &&
                    (txn_is_value[0] == std::byte(1) ||
                     txn_is_value[0] == std::byte(2))) {
                    txn_list = ((FreezerDB::rlp_item const
                                     *)(uintptr_t(txn_is_value.data()) + 1))
                                   ->list();
                }
                else {
                    unparsed_transactions++;
                    continue;
                }
            }
            else {
                txn_list = txn->list();
            }
            auto const *txn_list_end =
                (std::byte const *)txn_list.first + txn_list.second;
            bool found = false;
            for (auto const *item = txn_list.first->next(txn_list_end);
                 item != nullptr;
                 item = item->next(txn_list_end)) {
                auto const to_address = item->value();
                if (to_address.size() == 20) {
                    auto const *to_address2 =
                        (eth_address const *)to_address.data();
                    if (seen.end() == seen.find(*to_address2)) {
                        auto v = ++map[*to_address2];
                        if (v > largest_count) {
                            largest_count = v;
                        }
                        seen.insert(*to_address2);
                        ++total_transactions;
                        ++transactions_per_block[idx - blockno_begin];
                    }
                    found = true;
                    break;
                }
            }
            if (!found) {
                unparsed_transactions++;
            }
        }
    }
    static constexpr size_t CUTOFFS = 20;
    std::vector<std::pair<uint32_t, eth_address>> ranked;
    ranked.reserve(map.size());
    for (auto const &i : map) {
        ranked.emplace_back(i.second, i.first);
    }
    std::sort(ranked.rbegin(), ranked.rend());
    uint32_t const cutoff = uint32_t(total_transactions / CUTOFFS);
    uint32_t accounts[CUTOFFS + 1]{};
    uint32_t accum[CUTOFFS + 1]{};
    size_t n = 0;
    for (auto &i : ranked) {
        if (accum[n] + i.first >= cutoff) {
            n++;
            accum[n] = accum[n - 1] + i.first - cutoff;
        }
        accum[n] += i.first;
        accounts[n]++;
    }
    accounts[CUTOFFS - 1] += accounts[CUTOFFS];
    std::sort(transactions_per_block.begin(), transactions_per_block.end());
    std::ofstream out(outpath / (std::to_string(blockno_begin) + ".json"));
    out.exceptions(std::ofstream::badbit | std::ofstream::failbit);
    out << "{ \"total parsed transactions\": " << total_transactions
        << ", \"total accounts seen\": " << map.size()
        << ", \"parse failed transactions\": " << unparsed_transactions
        << ", \"transactions per block\": { \"median\": "
        << transactions_per_block[transactions_per_block.size() / 2]
        << ", \"mean\": "
        << (total_transactions / transactions_per_block.size())
        << ", \"max\": " << transactions_per_block.back() << " }";
    for (n = 0; n < CUTOFFS; n++) {
        out << ", \"<= " << ((n + 1) * (100 / CUTOFFS))
            << "%\": " << accounts[n];
    }
    out << "}\n";
    return unparsed_transactions;
}

int main(int argc, char *argv[])
{
    CLI::App cli{"geth_freezer_db_analyser"};
    try {
        std::filesystem::path outpath = "histograms";
        // std::filesystem::path dbpath =
        //     "/mnt/raid0/monad/monad-trie/perf_test/chaindata/ancient";
        std::filesystem::path dbpath =
            "/mnt/raid0/blockchain/data/geth/chaindata/ancient";
        unsigned granularity = 1000000;

        cli.add_option("--out", outpath, "path to where to write histograms");
        cli.add_option(
            "--dbpath", dbpath, "path to geth freezer db ('ancient')");
        cli.add_option(
            "--granularity", granularity, "size of bucket for statistics");
        cli.parse(argc, argv);

        FreezerDB db(dbpath);
        std::cout << "Opened geth freezer db at " << dbpath
                  << ". It has tables:";
        for (auto const &table : db.tables()) {
            std::cout << "\n   " << table.name() << " type "
                      << (table.is_compressed() ? "compressed" : "uncompressed")
                      << " with " << table.size() << " entries consuming "
                      << (double(table.bytes_consumed()) / 1024.0 / 1024.0 /
                          1024.0)
                      << " Gb.";
        }
        std::cout << "\nThis program was "
#if !MONAD_GETH_FREEZER_DB_HAVE_SNAPPY_H
                     "NOT "
#endif
                     "compiled with compression support."
                  << std::endl;

        // Useful for diagnosing parser errors
        auto print_body = [&](size_t idx) {
            std::byte buffer[4 * 1024 * 1024];
            auto contents = db.tables()[0].contents(buffer, idx);
            std::cout << "   Bodies has total length of " << contents.size()
                      << " bytes. Contents:\n";
            auto print_rlp = [](auto &self,
                                size_t indent,
                                std::span<std::byte const>
                                    contents) -> void {
                for (size_t n = 0; n < indent; n++) {
                    std::cout << " ";
                }
                for (auto const *i =
                         (FreezerDB::rlp_item const *)contents.data();
                     i;
                     i = i->next(contents.data() + contents.size())) {
                    auto v = i->value();
                    if (!v.empty()) {
                        std::cout << "v(" << v.size() << ") ";
                    }
                    else {
                        auto l = i->list();
                        if (l.second == 0) {
                            std::cout << "l(0) ";
                        }
                        else {
                            std::cout << "l(" << l.second << "):\n";
                            self(
                                self,
                                indent + 3,
                                {(const std::byte *)l.first, l.second});
                            for (size_t n = 0; n < indent; n++) {
                                std::cout << " ";
                            }
                        }
                    }
                }
                std::cout << "\n";
            };
            print_rlp(print_rlp, 3, contents);
            std::cout << std::endl;
        };
        (void)print_body;
        // std::cout << "\n\nFor bodies for block 13,000,000:\n";
        // print_body(13000000);
        // std::cout << "\n\nFor bodies for block 18,000,000:\n";
        // print_body(18000000);

        std::filesystem::create_directories(outpath);
        std::vector<std::future<std::pair<size_t, uint32_t>>> concurrency(
            std::thread::hardware_concurrency());
        auto const upper_block_no =
            (db.tables()[0].size() - (db.tables()[0].size() % granularity));
        size_t block_no = 0;
        for (;;) {
            bool still_working = false;
            for (auto &fut : concurrency) {
                if (fut.valid() && fut.wait_for(std::chrono::seconds(0)) ==
                                       std::future_status::ready) {
                    auto [thisblockno, failed_parses] = fut.get();
                    if (failed_parses > 0) {
                        std::cout << "   WARNING: block region " << thisblockno
                                  << "-" << (thisblockno + granularity - 1)
                                  << " had " << failed_parses
                                  << " failed transaction parses!" << std::endl;
                    }
                }
                if (!fut.valid()) {
                    if (block_no < upper_block_no) {
                        std::cout << "Starting work on blocks " << block_no
                                  << "-" << (block_no + granularity - 1)
                                  << " ..." << std::endl;
                        fut = std::async(
                            std::launch::async,
                            [=, &db]() -> std::pair<size_t, uint32_t> {
                                return {
                                    block_no,
                                    calculate_histogram_by_transaction(
                                        outpath,
                                        db.tables()[0],
                                        block_no,
                                        block_no + granularity)};
                            });
                        block_no += granularity;
                        still_working = true;
                    }
                }
                else {
                    still_working = true;
                }
            }
            if (!still_working) {
                break;
            }
        }
    }
    catch (const CLI::CallForHelp &e) {
        std::cout << cli.help() << std::flush;
    }
    catch (std::exception const &e) {
        std::cerr << "FATAL: " << e.what() << std::endl;
        return 1;
    }
    return 0;
}
