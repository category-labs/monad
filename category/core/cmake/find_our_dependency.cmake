if(FIND_OUR_DEPENDENCY_INCLUDED)
  return()
endif()
set(FIND_OUR_DEPENDENCY_INCLUDED 1)

# Because cmake has multiple ways of finding a dependency, this convenience
# function tries several of them on your behalf. Args:
#
# REQUIRED: Fail if not found.
# NOQUIET: Have each finding mechanism print what it does.
# IMPORTED_TARGET: What cmake target to declare. It should contain '::'
# so cmake knows it is an imported target, and prints appropriate
# diagnostics.

find_package(PkgConfig REQUIRED)
function(find_our_dependency name)
  cmake_parse_arguments(FIND_DEPENDENCY "REQUIRED;NOQUIET" "IMPORTED_TARGET" "" ${ARGN})
  if(FIND_DEPENDENCY_NOQUIET)
    set(QUIET "")
  else()
    set(QUIET "QUIET")
  endif()
  if(NOT FIND_DEPENDENCY_IMPORTED_TARGET)
    set(FIND_DEPENDENCY_IMPORTED_TARGET "${name}::${name}")
  elseif(NOT FIND_DEPENDENCY_IMPORTED_TARGET MATCHES ".*::.*")
    message(FATAL_ERROR "FATAL: IMPORTED_TARGET should have '::' in its name so cmake prints appropriate diagnostics")
  endif()

  if(NOT TARGET ${FIND_DEPENDENCY_IMPORTED_TARGET})
    # Used to create an imported cmake target when needed
    macro(make_imported_target)
      if(NOT EXISTS "${${name}_LIBRARY}")
        message(FATAL_ERROR "FATAL: ${name}_LIBRARY=${${name}_LIBRARY} does not exist")
      endif()
      if(NOT EXISTS "${${name}_INCLUDE_DIR}")
        message(FATAL_ERROR "FATAL: ${name}_INCLUDE_DIR=${${name}_INCLUDE_DIR} does not exist")
      endif()
      add_library(${FIND_DEPENDENCY_IMPORTED_TARGET} UNKNOWN IMPORTED)
      set_target_properties(${FIND_DEPENDENCY_IMPORTED_TARGET} PROPERTIES
        IMPORTED_LOCATION "${${name}_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${${name}_INCLUDE_DIR}"
      )
    endmacro()

    # First ask cmake to check its package registry. C++ package managers will
    # register dependencies here, so if the dependency is supplied by a C++
    # package manager, it will be found now.
    find_package(${name} ${QUIET})
    if(${name}_FOUND)
      if(NOT TARGET ${FIND_DEPENDENCY_IMPORTED_TARGET})
        message(FATAL_ERROR "FATAL: IMPORTED_TARGET=${FIND_DEPENDENCY_IMPORTED_TARGET} does not equal the target defined by find_package(${name}), which successfully found the dependency.")
      endif()
    else()
      # Second ask pkg-config for the local system for the dependency. Autotools
      # will register packages here, cmake may also do so if you install a package.
      pkg_check_modules(${name} ${QUIET} IMPORTED_TARGET ${FIND_DEPENDENCY_IMPORTED_TARGET})
      if(NOT ${name}_FOUND)
        # Third simply ask the local OS installation for the dependency.
        find_library(${name}_LIBRARY NAMES "${name}" ${QUIET})
        if(${name}_LIBRARY)
          find_path(${name}_INCLUDE_DIR NAMES "${name}.h" ${QUIET})
          make_imported_target()
        endif()
      endif()
    endif()
    if(FIND_DEPENDENCY_REQUIRED AND NOT TARGET ${FIND_DEPENDENCY_IMPORTED_TARGET})
      message(FATAL_ERROR "FATAL: None of find_package(), pkg_check_modules() nor find_library() found dependency '${name}'")
    endif()
  endif()
endfunction()
