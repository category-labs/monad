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

add_executable(parser-tool)

target_sources(parser-tool PRIVATE
  parser_tool.cpp)

target_include_directories(parser-tool
  PUBLIC src/
)

target_link_libraries(parser-tool
  PRIVATE monad_execution
  PRIVATE evmc::evmc
  PRIVATE CLI11::CLI11
)

monad_compile_options(parser-tool)
