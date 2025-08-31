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

add_trie_test(TARGET append_test SOURCES "append_test.cpp")
add_trie_test(TARGET big_endian_serialization_test SOURCES
              "big_endian_serialization_test.cpp")
add_trie_test(
  TARGET
  cli_tool_test
  SOURCES
  "cli_tool_test.cpp"
  "../cli_tool_impl.cpp"
  LINK_LIBRARIES
  PkgConfig::zstd
  PkgConfig::archive)
add_trie_test(TARGET compaction_test SOURCES "compaction_test.cpp")
add_trie_test(TARGET db_metadata_test SOURCES "db_metadata_test.cpp")
add_trie_test(TARGET update_aux_test SOURCES "update_aux_test.cpp")
add_trie_test(TARGET db_test SOURCES "db_test.cpp")
add_trie_test(TARGET fiber_future_wrapped_find_test SOURCES
              "fiber_future_wrapped_find.cpp")
add_trie_test(TARGET fiber_future_wrapped_read_test SOURCES
              "fiber_future_wrapped_read.cpp")
add_trie_test(TARGET load_all_test SOURCES "load_all_test.cpp")
add_trie_test(TARGET locking_trie_test SOURCES "locking_trie_test.cpp"
              LINK_LIBRARIES Boost::thread)
add_trie_test(TARGET many_nested_updates SOURCES "many_nested_updates.cpp"
              LINK_LIBRARIES Boost::json)
add_trie_test(TARGET merkle_trie_test SOURCES "merkle_trie_test.cpp")
add_trie_test(TARGET min_truncated_offsets_test SOURCES
              "min_truncated_offsets_test.cpp")
add_trie_test(TARGET mixed_async_sync_loads_test SOURCES
              "mixed_async_sync_loads_test.cpp")
add_trie_test(TARGET blocking_read_concurrency_test SOURCES
              "blocking_read_concurrency_test.cpp")
add_trie_test(TARGET nibbles_view_test SOURCES "nibbles_view_test.cpp")
add_trie_test(TARGET node_disk_pages_spare_test SOURCES
              "node_disk_pages_spare_test.cpp")
add_trie_test(TARGET node_test SOURCES "node_test.cpp")
add_trie_test(TARGET node_writer_test SOURCES "node_writer_test.cpp")
add_trie_test(TARGET plain_trie_test SOURCES "plain_trie_test.cpp")
add_trie_test(TARGET rewind_test SOURCES "rewind_test.cpp")
add_trie_test(TARGET state_machine_test SOURCES "state_machine_test.cpp")
add_trie_test(TARGET subtrie_version_test SOURCES "subtrie_version_test.cpp")
add_trie_test(TARGET unsigned_20_test SOURCES "unsigned_20_test.cpp")
add_trie_test(TARGET virtual_offset_test SOURCES "virtual_offset_test.cpp")

# monad trie perf test
add_executable(monad_trie_test "monad_trie_test.cpp")
monad_compile_options(monad_trie_test)
target_include_directories(monad_trie_test
                           PRIVATE "${PROJECT_SOURCE_DIR}/third_party")
target_link_libraries(monad_trie_test PUBLIC monad_execution CLI11::CLI11
                      quill::quill)

add_executable(monad_trie_test_statistical_generation_test
               "monad_trie_test_statistical_generation_test.cpp")
monad_compile_options(monad_trie_test_statistical_generation_test)
target_link_libraries(monad_trie_test_statistical_generation_test
                      PUBLIC monad_core)

# stress test
add_executable(read_only_db_stress_test "read_only_db_stress_test.cpp")
monad_compile_options(read_only_db_stress_test)
target_link_libraries(
  read_only_db_stress_test PUBLIC monad_execution CLI11::CLI11 quill::quill)

add_subdirectory("geth_freezer_db_analyzer")
