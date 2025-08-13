C_LICENSE_HEADER="\
// Copyright (C) 2025 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>."

PYTHON_LICENSE_HEADER="\
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
# along with this program.  If not, see <http://www.gnu.org/licenses/>."

# Check for two newlines after the license header
C_LICENSE_HEADER_LEN=$(("${#C_LICENSE_HEADER}" + 2))
PYTHON_LICENSE_HEADER_LEN=$(("${#PYTHON_LICENSE_HEADER}" + 2))

exit_code=0

for file in $(git ls-files -- '*.rs' '*.h' '*.hpp' '*.c' '*.cpp'); do
    contents=$(head -c $C_LICENSE_HEADER_LEN "$file")

    if [ "$contents" == "$C_LICENSE_HEADER" ]; then
        continue
    fi

    exit_code=$((exit_code + 1))

    echo "$file" >&2
done

for file in $(git ls-files -- '*.py' '*CMakeLists.txt'); do
    contents=$(head -c $PYTHON_LICENSE_HEADER_LEN "$file")

    if [ "$contents" == "$PYTHON_LICENSE_HEADER" ]; then
        continue
    fi

    exit_code=$((exit_code + 1))

    echo "$file" >&2
done

exit $exit_code
