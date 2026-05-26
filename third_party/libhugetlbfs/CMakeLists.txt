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

# This cmake project can be used to build just the execution event SDK library
# (as `libmonad_event.a`) without building all of the monolithic
# libmonad_execution.a or including the rest of the CMake build system. This
# is useful for external third-party clients, and for the Rust build system.

include(ExternalProject)

# libhugetlbfs
set(LIBHUGETLBFS_INSTALL_DIR ${CMAKE_BINARY_DIR}/libhugetlbfs-install)
ExternalProject_Add(
  libhugetlbfs_ext
  DOWNLOAD_COMMAND ""
  SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/src"
  PREFIX ${CMAKE_BINARY_DIR}/libhugetlbfs
  INSTALL_DIR ${LIBHUGETLBFS_INSTALL_DIR}
  CONFIGURE_COMMAND COMMAND /bin/sh autogen.sh
                   COMMAND env CC=${CMAKE_C_COMPILER} ./configure --prefix=${LIBHUGETLBFS_INSTALL_DIR}
  BUILD_COMMAND make -C <SOURCE_DIR> libs CC=${CMAKE_C_COMPILER} PREFIX=${LIBHUGETLBFS_INSTALL_DIR}
               BUILDTYPE=NATIVEONLY
  INSTALL_COMMAND make -C <SOURCE_DIR> install-libs CC=${CMAKE_C_COMPILER} PREFIX=${LIBHUGETLBFS_INSTALL_DIR}
                  BUILDTYPE=NATIVEONLY
  BUILD_IN_SOURCE 1
  BUILD_BYPRODUCTS ${LIBHUGETLBFS_INSTALL_DIR}/lib64/libhugetlbfs.a
                   ${LIBHUGETLBFS_INSTALL_DIR}/lib64/libhugetlbfs.so)
add_library(libhugetlbfs_shared SHARED IMPORTED GLOBAL)
add_library(libhugetlbfs_static STATIC IMPORTED GLOBAL)
add_dependencies(libhugetlbfs_shared libhugetlbfs_ext)
add_dependencies(libhugetlbfs_static libhugetlbfs_ext)
file(MAKE_DIRECTORY ${LIBHUGETLBFS_INSTALL_DIR}/include)
set_target_properties(
  libhugetlbfs_shared libhugetlbfs_static
  PROPERTIES INTERFACE_INCLUDE_DIRECTORIES ${LIBHUGETLBFS_INSTALL_DIR}/include)
set_target_properties(libhugetlbfs_shared
  PROPERTIES IMPORTED_LOCATION ${LIBHUGETLBFS_INSTALL_DIR}/lib64/libhugetlbfs.so)
set_target_properties(libhugetlbfs_static
  PROPERTIES IMPORTED_LOCATION ${LIBHUGETLBFS_INSTALL_DIR}/lib64/libhugetlbfs.a)
target_compile_definitions(libhugetlbfs_static INTERFACE MONAD_LIBHUGETLBFS_STATIC)
if(BUILD_SHARED_LIBS)
  add_library(libhugetlbfs ALIAS libhugetlbfs_shared)
else()
  add_library(libhugetlbfs ALIAS libhugetlbfs_static)
endif()
