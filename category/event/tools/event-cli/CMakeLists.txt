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

# We need to link against libstdc++15 but it may not be available at runtime
# on Ubuntu 24.04; allow it to be statically linked to support that platform
option(MONAD_EVENT_CLI_STATIC_CXX
       "Force event-cli to statically link the C++ standard library" OFF)

# This still requires -lstdc++exp as of GCC15 and -fexperimental-library
# as of clang 21; on macOS it's difficult to configure at all, because a
# non-system compiler will by default try linking the system runtime which
# won't have this even with -fexperimental-library
option(MONAD_EVENT_CLI_USE_CHRONO_TIME_ZONE
       "Use the <chrono> support for timezones" OFF)

if(CMAKE_CXX_COMPILER_ID STREQUAL "GNU" AND
   CMAKE_CXX_COMPILER_VERSION VERSION_LESS "15.2")
  message(FATAL_ERROR "gcc 15.2 or greater is required")
endif()

if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang" AND
   CMAKE_CXX_COMPILER_VERSION VERSION_LESS "19")
  message(FATAL_ERROR "clang 19 or greater is required")
endif()

find_package(CLI11 REQUIRED)
find_package(OpenSSL REQUIRED COMPONENTS Crypto)
find_package(zstd REQUIRED)

add_executable(event-cli
  blockstat.cpp
  command.hpp
  digest.cpp
  driver.cpp
  dump.cpp
  err_cxx.hpp
  execstat.cpp
  file.cpp
  file.hpp
  headstat.cpp
  info.cpp
  init.cpp
  init.hpp
  iterator.cpp
  iterator.hpp
  metadata.hpp
  options.hpp
  parse.cpp
  parse.hpp
  record.cpp
  recordexec.cpp
  run.cpp
  sectiondump.cpp
  snapshot.cpp
  stats.cpp
  stats.hpp
  stacktrace.cpp
  stream.cpp
  stream.hpp
  util.cpp
  util.hpp)

target_compile_definitions(event-cli PRIVATE _GNU_SOURCE)
target_compile_definitions(event-cli PRIVATE ZSTD_STATIC_LINKING_ONLY)
target_compile_features(event-cli PRIVATE cxx_std_23)
target_compile_options(event-cli PRIVATE -Wall -Wextra -Wconversion -Werror)

# Disable some warnings
target_compile_options(event-cli PRIVATE -Wno-c99-designator)
target_compile_options(event-cli PRIVATE -Wno-missing-field-initializers)

target_link_libraries(event-cli PRIVATE
    monad_event CLI11::CLI11 zstd::libzstd_static OpenSSL::Crypto)

if(MONAD_EVENT_CLI_USE_CHRONO_TIME_ZONE)
  target_compile_definitions(event-cli PRIVATE USE_CHRONO_TIME_ZONE)
endif()

include(CheckCXXSymbolExists)
check_cxx_symbol_exists(__GLIBCXX__ version STDLIB_IS_LIBSTDCXX)
check_cxx_symbol_exists(_LIBCPP_VERSION version STDLIB_IS_LIBCXX)

# Needed for now, for <stacktrace>
if(STDLIB_IS_LIBSTDCXX)
  target_link_libraries(event-cli PRIVATE -lstdc++exp)
endif()

if(MONAD_EVENT_CLI_STATIC_CXX)
  if(STDLIB_IS_LIBSTDCXX)
    target_link_options(event-cli PRIVATE -static-libstdc++)
  else()
    message(FATAL_ERROR "static libc++ not supported yet")
  endif()
endif()

set_target_properties(event-cli PROPERTIES RUNTIME_OUTPUT_NAME monad-event-cli)

install(TARGETS event-cli)
