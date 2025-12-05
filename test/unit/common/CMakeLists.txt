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

add_library(
  monad_unit_test_common STATIC
  ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/config.hpp
  ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/environment.hpp
  ${PROJECT_SOURCE_DIR}/test/unit/common/include/monad/test/traits_test.hpp
)

target_include_directories(
  monad_unit_test_common PUBLIC ${PROJECT_SOURCE_DIR}/test/unit/common/include)
set_target_properties(monad_unit_test_common PROPERTIES LINKER_LANGUAGE CXX)
target_link_libraries(monad_unit_test_common PUBLIC monad_execution_native)
monad_compile_options(monad_unit_test_common)
