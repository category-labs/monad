# Copyright (C) 2025-26 Category Labs, Inc.
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

project(monad_domain_execution)

add_library(
  monad_domain_execution OBJECT
  # domain
  "chain_id.cpp"
  "chain_id.hpp"
  "config.hpp"
  "derivation_error.cpp"
  "derivation_error.hpp"
  "derive_domain_block.cpp"
  "derive_domain_block.hpp"
  "domain_block.hpp"
  "hpke.cpp"
  "hpke.hpp"
  "inputs.hpp"
  "l1_source.cpp"
  "l1_source.hpp"
  "scan_domain_inputs.cpp"
  "scan_domain_inputs.hpp"
  "system_transaction.cpp"
  "system_transaction.hpp")

target_link_libraries(
  monad_domain_execution
  PUBLIC monad_execution_native
  PRIVATE aws_lc::crypto)
monad_compile_options(monad_domain_execution)

file(GLOB_RECURSE domain_tests CONFIGURE_DEPENDS *_test.cpp)
foreach(test_file ${domain_tests})
  get_filename_component(test_name ${test_file} NAME_WLE)
  monad_add_test(${test_name} ${test_file})
  target_link_libraries(${test_name} monad_domain_execution)
endforeach()
