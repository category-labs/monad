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

find_program(DUNE dune REQUIRED)

set(LIBMONADML_EVM "${CMAKE_SOURCE_DIR}/third_party/monad-execution-specs/_build/default/bindings/vm/libmonadml_evm.so")

add_custom_target(build-monadml-evm ALL
    COMMAND ${DUNE} build bindings/vm/libmonadml_evm.so --profile release
    WORKING_DIRECTORY ${CMAKE_SOURCE_DIR}/third_party/monad-execution-specs
    BYPRODUCTS ${LIBMONADML_EVM}
    COMMENT "Building OCaml VM reference implementation"
    VERBATIM
)

add_library(monadml-evm SHARED IMPORTED GLOBAL)

set_target_properties(monadml-evm PROPERTIES
  IMPORTED_LOCATION ${LIBMONADML_EVM}
  INTERFACE_INCLUDE_DIRECTORIES "${CMAKE_CURRENT_SOURCE_DIR}/.."
)

add_dependencies(monadml-evm build-monadml-evm)
