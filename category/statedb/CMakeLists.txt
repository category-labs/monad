# Copyright (C) 2025 Category Labs, Inc.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad_statedb)

# F1: the RocksDB state backend's home. The target exists and compiles in both
# configurations, but nothing consumes it yet — the KvStore, CF schema, and the
# rest of the RocksDbDb land in later PRs (F2+). When MONAD_ENABLE_ROCKSDB=ON it
# links the vendored RocksDB and defines MONAD_HAVE_ROCKSDB for conditional code.
add_library(monad_statedb OBJECT "statedb.cpp" "statedb.hpp")

target_include_directories(monad_statedb PUBLIC ${CATEGORY_MAIN_DIR})

monad_compile_options(monad_statedb)

if(MONAD_ENABLE_ROCKSDB)
  target_compile_definitions(monad_statedb PUBLIC MONAD_HAVE_ROCKSDB=1)
  target_link_libraries(monad_statedb PUBLIC RocksDB::rocksdb)
endif()
