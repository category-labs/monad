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

add_executable(mce)

target_sources(mce PRIVATE
  mce.cpp
  "src/instrumentable_decoder.hpp"
  "src/instrumentable_parser.hpp"
  "src/instrumentable_compiler.hpp"
  "src/instrumentable_vm.hpp"
  "src/instrumentation_device.hpp"
  "src/stopwatch.hpp")

target_include_directories(mce
  PUBLIC src/
  PUBLIC "${CATEGORY_MAIN_DIR}/third_party/evmone/test/state"
  PUBLIC "${CATEGORY_MAIN_DIR}/third_party/valgrind/cachegrind"
  PUBLIC "${CATEGORY_MAIN_DIR}/third_party/valgrind/include"
)

target_link_libraries(mce
  PRIVATE monad_execution
  PRIVATE evmone
  PRIVATE evmone::state
  PRIVATE CLI11::CLI11
  PRIVATE nlohmann_json::nlohmann_json
)

monad_compile_options(mce)
