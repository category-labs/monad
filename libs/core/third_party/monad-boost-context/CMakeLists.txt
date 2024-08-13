project(monad_boost_context VERSION "${MONAD_VERSION}" LANGUAGES ASM C)

# Binary format

if(WIN32)
  message(FATAL_ERROR "Win32 not supported")
elseif(APPLE)
  set(_default_binfmt mach-o)
else()
  set(_default_binfmt elf)
endif()

set(MONAD_BOOST_CONTEXT_BINARY_FORMAT "${_default_binfmt}" CACHE STRING "Boost.Context binary format (elf, mach-o)")
set_property(CACHE MONAD_BOOST_CONTEXT_BINARY_FORMAT PROPERTY STRINGS elf mach-o)

unset(_default_binfmt)

# ABI

if(CMAKE_SYSTEM_PROCESSOR MATCHES "^[Aa][Rr][Mm]" OR CMAKE_SYSTEM_PROCESSOR STREQUAL "aarch64")
  set(_default_abi aapcs)
else()
  set(_default_abi sysv)
endif()

set(MONAD_BOOST_CONTEXT_ABI "${_default_abi}" CACHE STRING "Boost.Context ABI (aapcs, sysv)")
set_property(CACHE MONAD_BOOST_CONTEXT_ABI PROPERTY STRINGS aapcs sysv)

unset(_default_abi)

# Arch-and-model

set(_all_archs arm64 x86_64)

# Try at start to auto determine arch from CMake.
if(CMAKE_SYSTEM_PROCESSOR IN_LIST _all_archs)
  set(_default_arch ${CMAKE_SYSTEM_PROCESSOR})
else()
  if(CMAKE_SYSTEM_PROCESSOR STREQUAL "aarch64")
    set(_default_arch arm64)
  else()
    set(_default_arch x86_64)
  endif()
endif()

set(MONAD_BOOST_CONTEXT_ARCHITECTURE "${_default_arch}" CACHE STRING "Boost.Context architecture (arm64, x86_64)")
set_property(CACHE MONAD_BOOST_CONTEXT_ARCHITECTURE PROPERTY STRINGS ${_all_archs})

unset(_all_archs)
unset(_default_arch)

message(STATUS "Boost.Context: "
  "architecture ${MONAD_BOOST_CONTEXT_ARCHITECTURE}, "
  "binary format ${MONAD_BOOST_CONTEXT_BINARY_FORMAT}, "
  "ABI ${MONAD_BOOST_CONTEXT_ABI}")

if(MONAD_BOOST_CONTEXT_BINARY_FORMAT STREQUAL mach-o)
  set(MONAD_BOOST_CONTEXT_BINARY_FORMAT macho)
endif()

set(_asm_suffix ${MONAD_BOOST_CONTEXT_ARCHITECTURE}_${MONAD_BOOST_CONTEXT_ABI}_${MONAD_BOOST_CONTEXT_BINARY_FORMAT}_gas.S)

set(ASM_SOURCES
  src/asm/make_${_asm_suffix}
  src/asm/jump_${_asm_suffix}
  src/asm/ontop_${_asm_suffix}
)

unset(_asm_suffix)

add_library(monad_boost_context ${ASM_SOURCES})
target_include_directories(monad_boost_context PUBLIC include)