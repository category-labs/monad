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

# The RocksDB state backend's home. The base target compiles in both
# configurations; nothing consumes it yet. The RocksDB-only sources (CF schema +
# KvStore, F2) and the rest of the RocksDbDb (F6+) build only when the backend is
# enabled, defining MONAD_HAVE_ROCKSDB and linking the vendored RocksDB.
add_library(monad_statedb OBJECT "statedb.cpp" "statedb.hpp")

target_include_directories(monad_statedb PUBLIC ${CATEGORY_MAIN_DIR})

monad_compile_options(monad_statedb)

if(MONAD_ENABLE_ROCKSDB)
  target_sources(
    monad_statedb
    PRIVATE "kv_store.cpp"
            "kv_store.hpp"
            "schema.hpp"
            "trie_node_store.cpp"
            "trie_node_store.hpp")
  target_compile_definitions(monad_statedb PUBLIC MONAD_HAVE_ROCKSDB=1)
  target_link_libraries(monad_statedb PUBLIC RocksDB::rocksdb monad_core)

  # Leaf-lib unit tests: link monad_statedb + RocksDB only, not the full engine.
  # monad_core provides MONAD_ASSERT's handler (monad_assertion_failed); name it
  # explicitly since these leaf tests link monad_statedb directly rather than the
  # monad_execution aggregate, and OBJECT-library objects don't propagate
  # transitively to the final executable.
  add_unit_test(
    TARGET test_kv_store
    SOURCES test_kv_store.cpp
    LIBRARIES monad_statedb monad_core RocksDB::rocksdb)
  add_unit_test(
    TARGET test_trie_node_store
    SOURCES test_trie_node_store.cpp
    LIBRARIES monad_statedb monad_core RocksDB::rocksdb)
endif()
