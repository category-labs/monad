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

function(monad_configure_boost_outcome_status_code_overlay out_var)
  set(_flat_base "boost/outcome/experimental/status-code")
  set(_nested_base "boost/outcome/experimental/status-code/status-code")

  set(_boost_include_dirs ${Boost_INCLUDE_DIRS})
  if(NOT _boost_include_dirs AND TARGET Boost::headers)
    get_target_property(_boost_include_dirs Boost::headers
                        INTERFACE_INCLUDE_DIRECTORIES)
  endif()

  if(NOT _boost_include_dirs)
    message(
      FATAL_ERROR
        "Boost include directories are unknown; cannot configure Boost.Outcome status-code overlay"
    )
  endif()

  set(_flat_root)
  set(_nested_root)
  foreach(_include_dir IN LISTS _boost_include_dirs)
    if(NOT _flat_root
       AND EXISTS "${_include_dir}/${_flat_base}/config.hpp")
      set(_flat_root "${_include_dir}")
    endif()
    if(NOT _nested_root
       AND EXISTS "${_include_dir}/${_nested_base}/config.hpp")
      set(_nested_root "${_include_dir}")
    endif()
  endforeach()

  set(_overlay_dir
      "${CMAKE_BINARY_DIR}/generated/boost-outcome-status-code-overlay")
  set_property(GLOBAL PROPERTY MONAD_BOOST_INCLUDE_DIRS
                               "${_boost_include_dirs}")

  if(_flat_root)
    if(_nested_root AND NOT _nested_root STREQUAL _flat_root)
      message(
        WARNING
          "Selected Boost include directories expose both flat and nested "
          "Boost.Outcome status-code layouts from different roots; using "
          "flat layout from ${_flat_root}; nested layout was found at "
          "${_nested_root}"
      )
    else()
      message(
        STATUS
          "Using Boost.Outcome status-code flat include layout from ${_flat_root}"
      )
    endif()

    # The source tree uses the flat include spelling, so no overlay is needed.
    file(REMOVE_RECURSE "${_overlay_dir}")
    set_property(GLOBAL PROPERTY MONAD_BOOST_OUTCOME_STATUS_CODE_OVERLAY_DIR "")
    set(${out_var}
        ""
        PARENT_SCOPE)
    return()
  elseif(_nested_root)
    set(_source_root "${_nested_root}")
    set(_source_base "${_nested_base}")
    set(_wrapper_base "${_flat_base}")
  else()
    list(JOIN _boost_include_dirs "\n  " _boost_include_dirs_pretty)
    message(
      FATAL_ERROR
        "Could not find Boost.Outcome status-code headers under selected Boost include directories:\n  ${_boost_include_dirs_pretty}"
    )
  endif()

  # Monad only includes top-level status-code headers directly. Forwarded
  # nested headers resolve their own detail/ siblings relative to themselves.
  file(GLOB _status_code_headers CONFIGURE_DEPENDS
       "${_source_root}/${_source_base}/*.hpp")
  if(NOT _status_code_headers)
    message(
      FATAL_ERROR
        "No Boost.Outcome status-code headers found under ${_source_root}/${_source_base}"
    )
  endif()

  file(MAKE_DIRECTORY "${_overlay_dir}/${_wrapper_base}")
  file(REMOVE_RECURSE "${_overlay_dir}/${_nested_base}")
  set(_generated_headers)
  foreach(_header IN LISTS _status_code_headers)
    get_filename_component(_header_name "${_header}" NAME)
    set(_header_path "${_overlay_dir}/${_wrapper_base}/${_header_name}")
    set(_header_content
        "#pragma once\n#include <${_source_base}/${_header_name}>\n")
    list(APPEND _generated_headers "${_header_path}")

    if(EXISTS "${_header_path}")
      file(READ "${_header_path}" _existing_header_content)
    else()
      set(_existing_header_content)
    endif()

    if(NOT _existing_header_content STREQUAL _header_content)
      file(WRITE "${_header_path}" "${_header_content}")
    endif()
  endforeach()

  file(GLOB _existing_headers CONFIGURE_DEPENDS
       "${_overlay_dir}/${_wrapper_base}/*.hpp")
  foreach(_header IN LISTS _existing_headers)
    if(NOT _header IN_LIST _generated_headers)
      file(REMOVE "${_header}")
    endif()
  endforeach()

  message(
    STATUS
      "Generated Boost.Outcome status-code include overlay for ${_wrapper_base} from ${_source_root}/${_source_base}"
  )
  set_property(GLOBAL PROPERTY MONAD_BOOST_OUTCOME_STATUS_CODE_OVERLAY_DIR
                               "${_overlay_dir}")
  set(${out_var}
      "${_overlay_dir}"
      PARENT_SCOPE)
endfunction()

function(monad_target_include_boost_outcome_status_code_overlay target)
  if(NOT TARGET "${target}")
    message(FATAL_ERROR "Unknown target: ${target}")
  endif()

  get_property(_overlay_dir GLOBAL PROPERTY
               MONAD_BOOST_OUTCOME_STATUS_CODE_OVERLAY_DIR)
  if(NOT _overlay_dir AND MONAD_BOOST_OUTCOME_STATUS_CODE_OVERLAY_DIR)
    set(_overlay_dir "${MONAD_BOOST_OUTCOME_STATUS_CODE_OVERLAY_DIR}")
  endif()

  get_property(_boost_include_dirs GLOBAL PROPERTY MONAD_BOOST_INCLUDE_DIRS)
  if(NOT _boost_include_dirs AND Boost_INCLUDE_DIRS)
    set(_boost_include_dirs ${Boost_INCLUDE_DIRS})
  endif()

  set(_include_dirs)
  if(_overlay_dir)
    list(APPEND _include_dirs "$<BUILD_INTERFACE:${_overlay_dir}>")
  endif()
  foreach(_include_dir IN LISTS _boost_include_dirs)
    list(APPEND _include_dirs "$<BUILD_INTERFACE:${_include_dir}>")
  endforeach()

  if(_include_dirs)
    target_include_directories("${target}" BEFORE PUBLIC ${_include_dirs})
  endif()
endfunction()
