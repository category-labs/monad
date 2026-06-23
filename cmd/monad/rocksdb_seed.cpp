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

// F8 offline seed: convert a monad_db_dump_snapshot filesystem snapshot into a
// RocksDB store usable by `monad --state-backend=rocksdb`. Built only when
// -DMONAD_ENABLE_ROCKSDB=ON (the loader is otherwise compiled out).

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/db/snapshot_loader.hpp>

#include <CLI/CLI.hpp>

#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <string>

namespace fs = std::filesystem;

int main(int const argc, char const *argv[])
{
    CLI::App cli{
        "Seed a RocksDB store from a monad_db_dump_snapshot filesystem "
        "snapshot (F8).",
        "monad-rocksdb-seed"};

    fs::path snapshot_dir;
    uint64_t block = 0;
    fs::path rocksdb_dir;

    cli.add_option(
           "--snapshot-dir",
           snapshot_dir,
           "parent directory containing the per-block snapshot (i.e. the "
           "directory that holds <block>/)")
        ->required();
    cli.add_option(
           "--block",
           block,
           "block number of the snapshot to load (the <block> subdirectory)")
        ->required();
    cli.add_option(
           "--rocksdb-dir",
           rocksdb_dir,
           "output RocksDB store directory (created if absent)")
        ->required();

    CLI11_PARSE(cli, argc, argv);

    std::fprintf(
        stderr,
        "Seeding RocksDB at %s from snapshot %s (block %lu)...\n",
        rocksdb_dir.c_str(),
        (snapshot_dir / std::to_string(block)).c_str(),
        static_cast<unsigned long>(block));

    monad::bytes32_t const state_root =
        monad::seed_rocksdb_from_snapshot(snapshot_dir, block, rocksdb_dir);

    std::string hex = "0x";
    static constexpr char digits[] = "0123456789abcdef";
    for (unsigned char const b : state_root.bytes) {
        hex += digits[b >> 4];
        hex += digits[b & 0x0f];
    }
    std::printf("seeded state_root = %s\n", hex.c_str());
    return 0;
}
