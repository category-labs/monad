#!/bin/bash

C_LICENSE_LINES=(
    "^// Copyright \(C\) 2025(-26)? Category Labs, Inc\.$"
    "//"
    "// This program is free software: you can redistribute it and/or modify"
    "// it under the terms of the GNU General Public License as published by"
    "// the Free Software Foundation, either version 3 of the License, or"
    "// (at your option) any later version."
    "//"
    "// This program is distributed in the hope that it will be useful,"
    "// but WITHOUT ANY WARRANTY; without even the implied warranty of"
    "// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the"
    "// GNU General Public License for more details."
    "//"
    "// You should have received a copy of the GNU General Public License"
    "// along with this program.  If not, see <http://www.gnu.org/licenses/>."
)

PYTHON_LICENSE_LINES=(
    "^# Copyright \(C\) 2025(-26)? Category Labs, Inc\.$"
    "#"
    "# This program is free software: you can redistribute it and/or modify"
    "# it under the terms of the GNU General Public License as published by"
    "# the Free Software Foundation, either version 3 of the License, or"
    "# (at your option) any later version."
    "#"
    "# This program is distributed in the hope that it will be useful,"
    "# but WITHOUT ANY WARRANTY; without even the implied warranty of"
    "# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the"
    "# GNU General Public License for more details."
    "#"
    "# You should have received a copy of the GNU General Public License"
    "# along with this program.  If not, see <http://www.gnu.org/licenses/>."
)

NEW_C_LICENSE_LINES=("${C_LICENSE_LINES[@]}")
NEW_C_LICENSE_LINES[0]="^// Copyright \(C\) 2025-26 Category Labs, Inc\.$"

NEW_PYTHON_LICENSE_LINES=("${PYTHON_LICENSE_LINES[@]}")
NEW_PYTHON_LICENSE_LINES[0]="^# Copyright \(C\) 2025-26 Category Labs, Inc\.$"

# Function to check if a file has valid license header
check_license() {
    local file="$1"
    shift
    local patterns=("$@")
    local num_lines=${#patterns[@]}

    # Read the first num_lines (+1 for potential blank line) into an array
    mapfile -n $((num_lines + 1)) -t lines < "$file"

    # Check first line (copyright) with regex
    if ! [[ "${lines[0]}" =~ ${patterns[0]} ]]; then
        return 1
    fi

    # Check remaining lines with exact string comparison
    for ((i=1; i<num_lines; i++)); do
        if [[ "${lines[$i]}" != "${patterns[$i]}" ]]; then
            return 1
        fi
    done

    # If file has content beyond the header, check for blank line
    if [[ "${lines[$num_lines]}" != "" ]]; then
            return 1
    fi

    return 0
}

exit_code=0

# CI supplies the PR or push base ref; local runs also detect staged additions.
declare -A new_files

if [ -n "${LICENSE_BASE_REF:-}" ]; then
    if ! git rev-parse --verify --quiet "${LICENSE_BASE_REF}^{commit}" >/dev/null; then
        echo "license base ref does not exist: ${LICENSE_BASE_REF}" >&2
        exit 1
    fi

    while IFS= read -r -d '' file; do
        new_files["$file"]=1
    done < <(git diff --name-only --diff-filter=A -z "$LICENSE_BASE_REF" HEAD --)
fi

while IFS= read -r -d '' file; do
    new_files["$file"]=1
done < <(git diff --cached --name-only --diff-filter=A -z --)

for file in $(git ls-files -- '*.rs' '*.h' '*.hpp' '*.c' '*.cpp' '*.S'); do
    directory=$(dirname "$file")

    if [ "$directory" == "utils/clang-tidy-auto-const" ]; then
        continue
    fi

    if [ "$file" == "zkvm/core/zkvm_accelerators.h" ]; then
        continue
    fi

    if [ "${directory#third_party}" != "$directory" ]; then
        continue
    fi

    license_lines=("${C_LICENSE_LINES[@]}")
    if [ -n "${new_files[$file]+x}" ]; then
        license_lines=("${NEW_C_LICENSE_LINES[@]}")
    fi

    if check_license "$file" "${license_lines[@]}"; then
        continue
    fi

    exit_code=$((exit_code + 1))

    echo "$file" >&2
done

for file in $(git ls-files -- '*.py' '*CMakeLists.txt' '*.cmake'); do
    directory=$(dirname "$file")

    if [ "$directory" == "cmake/dummy" ]; then
        continue
    fi

    license_lines=("${PYTHON_LICENSE_LINES[@]}")
    if [ -n "${new_files[$file]+x}" ]; then
        license_lines=("${NEW_PYTHON_LICENSE_LINES[@]}")
    fi

    if check_license "$file" "${license_lines[@]}"; then
        continue
    fi

    exit_code=$((exit_code + 1))

    echo "$file" >&2
done

exit $exit_code
