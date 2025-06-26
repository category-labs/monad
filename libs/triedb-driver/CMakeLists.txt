cmake_minimum_required(VERSION 3.27)

cmake_policy(SET CMP0144 NEW) # find_package uses upper-case _ROOT variables

project(monad-triedb-driver LANGUAGES C CXX ASM)
enable_testing()

find_program(BINDGEN_PROGRAM bindgen REQUIRED)
find_program(RUSTC_PROGRAM rustc REQUIRED)

set(monad-triedb-driver_INCLUDES "src/monad/triedb-driver/triedb.h")

add_library(monad-triedb-driver ${monad-triedb-driver_INCLUDES} "src/monad/triedb-driver/triedb.cpp")
monad_compile_options(monad-triedb-driver)
target_link_libraries(monad-triedb-driver PRIVATE monad_trie)
target_link_libraries(monad-triedb-driver PUBLIC monad_core)
set_target_properties(monad-triedb-driver PROPERTIES
  POSITION_INDEPENDENT_CODE ON
)

add_custom_command(OUTPUT "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver_raw_bindings.rs"
  COMMAND "${BINDGEN_PROGRAM}" -o "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver_raw_bindings.rs"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/monad/triedb-driver/triedb.h"
  --allowlist-function "monad_c_.*"
  --allowlist-function "monad_c_triedb_.*"
  --allowlist-function "outcome_.*"
  --allowlist-type "monad_c_.*"
  --allowlist-type "monad_c_triedb_.*"
  --allowlist-type "outcome_.*"
  --allowlist-var "monad_c_.*"
  --allowlist-var "monad_c_triedb_.*"
  --allowlist-var "outcome_.*"
  --generate-inline-functions
  --no-layout-tests
  --no-doc-comments
  --no-copy "monad_c_.*"
  --no-copy "monad_c_triedb_.*"
  --no-copy "outcome_.*"
  --no-debug "cxx_status_code_system"
  --with-derive-default
  --must-use-type cxx_result_status_code_system_monad_async
  --
  "$<LIST:TRANSFORM,$<TARGET_PROPERTY:monad_core,INTERFACE_INCLUDE_DIRECTORIES>,PREPEND,-I>"
  -I ${CMAKE_CURRENT_LIST_DIR}/src
  DEPENDS ${monad-triedb-driver_INCLUDES}
  COMMAND_EXPAND_LISTS
  VERBATIM
)
add_custom_target(monad-triedb-driver_regenerate_rust_bindings DEPENDS "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver_raw_bindings.rs")
add_dependencies(monad-triedb-driver monad-triedb-driver_regenerate_rust_bindings)

cmake_host_system_information(RESULT linux_flavour QUERY DISTRIB_ID)
if(linux_flavour MATCHES "debian|ubuntu")
    find_package(Boost REQUIRED stacktrace_backtrace)
    add_library(boost_stacktrace_backtrace ALIAS Boost::stacktrace_backtrace)
    set(BOOST_STACKTRACE_LIB boost_stacktrace_backtrace)
else()
    find_package(Boost REQUIRED stacktrace_addr2line)
    add_library(boost_stacktrace_addr2line ALIAS Boost::stacktrace_addr2line)
    set(BOOST_STACKTRACE_LIB boost_stacktrace_addr2line)
endif()

function(append_link_string out target)
  get_target_property(imp ${target} IMPORTED)
  if(imp)
    get_target_property(loc ${target} LOCATION)
    if(loc)
      if(target MATCHES ".+::.+")
        cmake_path(GET loc PARENT_PATH dir)
        cmake_path(GET loc STEM leaf)
        if(leaf MATCHES "lib.+")
          string(SUBSTRING "${leaf}" 3 -1 leaf)
        endif()
        list(APPEND ${out} "-L${dir}")
        list(APPEND ${out} "-l${leaf}")
      else()
        list(APPEND ${out} "-l$<TARGET_NAME:${target}>")
      endif()
    endif()
  endif()
  if(TARGET ${target})
    get_target_property(nonaliased ${target} ALIASED_TARGET)
    if(nonaliased)
      set(target ${nonaliased})
    endif()
    get_target_property(libs ${target} LINK_LIBRARIES)
    if(libs)
      list(APPEND ${out} "-L$<TARGET_FILE_DIR:${target}>")
      list(APPEND ${out} "-l$<TARGET_NAME:${target}>")
      foreach(target ${libs})
        if(TARGET ${target})
          append_link_string(${out} ${target})
        else()
          list(APPEND ${out} "-l${target}")
        endif()
      endforeach()
    endif()
  endif()
  set(${out} ${${out}} PARENT_SCOPE)
endfunction()
set(linkstring)
append_link_string(linkstring monad-triedb-driver)
list(REMOVE_DUPLICATES linkstring)
add_custom_command(OUTPUT "${CMAKE_BINARY_DIR}/test/monad_triedb_driver_test"
  COMMAND "${RUSTC_PROGRAM}" --test -o "${CMAKE_BINARY_DIR}/test/monad_triedb_driver_test"
  "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver_test.rs"
  ${linkstring}
  -lstdc++
  DEPENDS
    "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver_test.rs"
    "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver_raw_bindings.rs"
    "${CMAKE_CURRENT_SOURCE_DIR}/rust/monad_triedb_driver.rs"
)
add_custom_target(monad-triedb-driver_rust_tests ALL DEPENDS "${CMAKE_BINARY_DIR}/test/monad_triedb_driver_test")
add_dependencies(monad-triedb-driver_rust_tests monad-triedb-driver)
add_test(NAME monad-triedb-driver_rust_tests COMMAND "${CMAKE_BINARY_DIR}/test/monad_triedb_driver_test" --nocapture)
