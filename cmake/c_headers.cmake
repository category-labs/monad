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

# Compile each C header on its own, as C
file(GLOB_RECURSE c_headers CONFIGURE_DEPENDS RELATIVE ${PROJECT_SOURCE_DIR}
     category/*.h)
list(FILTER c_headers EXCLUDE REGEX "_inline\\.h$")
foreach(header IN LISTS c_headers)
  string(MAKE_C_IDENTIFIER ${header} name)
  set(source ${CMAKE_CURRENT_BINARY_DIR}/c_headers/${name}.c)
  file(CONFIGURE OUTPUT ${source} CONTENT "#include <${header}>\n")
  list(APPEND c_header_sources ${source})
endforeach()
add_library(monad_c_headers OBJECT ${c_header_sources})
monad_compile_options(monad_c_headers)
target_link_libraries(monad_c_headers PRIVATE monad_execution)
