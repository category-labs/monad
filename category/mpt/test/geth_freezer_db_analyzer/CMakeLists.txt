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

# geth freezer db analyser
add_executable(geth_freezer_db_analyzer "geth_freezer_db_analyzer.cpp")
monad_compile_options(geth_freezer_db_analyzer)
target_link_libraries(geth_freezer_db_analyzer PUBLIC monad_core CLI11::CLI11)
find_library(libsnappy NAMES "snappy" QUIET)
if(libsnappy)
  target_link_libraries(geth_freezer_db_analyzer PUBLIC ${libsnappy})
endif()
