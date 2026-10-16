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

# Templates place each @variable@ inside a JSON string. Escape local copies
# so compiler flags and build-signature inputs remain unchanged in the caller.
function(monad_zkvm_configure_json input output)
    file(READ "${input}" _template)
    string(REGEX MATCHALL "@[A-Za-z0-9_]+@" _variables "${_template}")
    list(REMOVE_DUPLICATES _variables)
    foreach(_placeholder IN LISTS _variables)
        string(REPLACE "@" "" _name "${_placeholder}")
        set(_value "${${_name}}")
        string(REPLACE "\\" "\\\\" _value "${_value}")
        string(REPLACE "\"" "\\\"" _value "${_value}")
        # CMake strings cannot contain NUL; escape the other JSON controls.
        foreach(_code RANGE 1 31)
            string(ASCII ${_code} _char)
            string(HEX "${_char}" _hex)
            string(REPLACE "${_char}" "\\u00${_hex}" _value "${_value}")
        endforeach()
        set(${_name} "${_value}")
    endforeach()
    configure_file("${input}" "${output}" @ONLY)
endfunction()
