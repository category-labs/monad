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

function(monad_add_test target)
  add_executable(${target} ${ARGN})
  monad_compile_options(${target})
  target_link_libraries(${target} monad_core GTest::GTest GTest::Main)
  add_test(NAME ${target} COMMAND $<TARGET_FILE:${target}>)
endfunction()

monad_add_test(allocators_test "allocators.cpp")
monad_add_test(backtrace_test "backtrace.cpp")
monad_add_test(cpuset_test "cpuset.cpp")
monad_add_test(encode_test "encode_test.cpp")
monad_add_test(event_recorder "event_recorder.cpp")
set_tests_properties(event_recorder PROPERTIES RUN_SERIAL TRUE)
monad_add_test(hugemem_test "huge_mem.cpp")
target_link_libraries(hugemem_test GTest::gmock)
monad_add_test(hugetlbfs_path_test "hugetlbfs_path.cpp")
monad_add_test(io_buffers_test "io_buffers.cpp")
monad_add_test(literal_test "literal_test.cpp")
monad_add_test(log_ffi_test "log_ffi.cpp")
monad_add_test(monad_exception_test "monad_exception.cpp")
monad_add_test(priority_pool_test "priority_pool_test.cpp")
set_tests_properties(priority_pool_test PROPERTIES RUN_SERIAL TRUE)
monad_add_test(unordered_map_test "unordered_map.cpp")
