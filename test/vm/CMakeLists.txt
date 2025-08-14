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

include(GoogleTest)

if(MONAD_COMPILER_TESTING)
    find_package(GTest REQUIRED)
endif()

if(MONAD_COMPILER_BENCHMARKS)
    find_package(benchmark REQUIRED)
endif()

if(MONAD_COMPILER_BENCHMARKS)
  add_subdirectory(compile_benchmarks)
  add_subdirectory(execution_benchmarks)
  add_subdirectory(long_benchmarks)
  add_subdirectory(micro_benchmarks)
endif()

if(MONAD_COMPILER_TESTING)
  add_subdirectory(blockchain)
  add_subdirectory(fuzzer)
  add_subdirectory(unit)
endif()

if(MONAD_COMPILER_BENCHMARKS OR MONAD_COMPILER_TESTING)
  add_subdirectory(utils)
endif()

# The testing VM is shared between both the testing and benchmark setups, so we
# build it in both scenarios.
add_subdirectory(vm)
