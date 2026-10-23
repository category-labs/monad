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

# monad-bench, which benchmarks graphs for the graph-eval precompile and EVM
# bytecode in each engine that can run them; see main.cpp. It reads graphs as
# the graphcode, calldata and accounts files scripts/graphcode.py writes

add_executable(monad-bench main.cpp)
monad_compile_options(monad-bench)
target_link_libraries(
  monad-bench PRIVATE monad_execution monad-test-utils
                      monad-vm::monad-vm-test-utils CLI11::CLI11)
target_compile_definitions(
  monad-bench PRIVATE MONAD_BENCH_BUILD_TYPE="${CMAKE_BUILD_TYPE}")

# The compiled-graph modes, with the compilers built
if(MONAD_GRAPH_EVAL_IREE)
  target_compile_definitions(monad-bench PRIVATE MONAD_BENCH_IREE)
  target_link_libraries(monad-bench PRIVATE iree_compiler)
endif()
if(MONAD_GRAPH_EVAL_HALIDE)
  target_compile_definitions(monad-bench PRIVATE MONAD_BENCH_HALIDE)
  target_link_libraries(monad-bench PRIVATE halide)
endif()
if(MONAD_GRAPH_EVAL_XLA)
  target_compile_definitions(monad-bench PRIVATE MONAD_BENCH_XLA)
  target_link_libraries(monad-bench PRIVATE monad_xla)
endif()
