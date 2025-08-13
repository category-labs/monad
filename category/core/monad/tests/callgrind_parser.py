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

import re
import json
import fileinput


def parse(input):
    pattern_func = "^fn=\\([0-9]+\\).*(?=[\n])"
    pattern_callee = "^cfn=\\([0-9]+\\).*(?=[\n])"
    in_a_function = False
    in_callee_function = False
    name = ""
    id = -1
    id_to_name = {}
    name_to_instr_self = {}
    for line in input:
        matches = re.findall(pattern_func, line, re.MULTILINE)
        if len(matches) > 0:
            in_a_function = True
            in_callee_function = False
            id = re.split("[()]", matches[0])[1]
            if id not in id_to_name:
                name = matches[0].split(" ", 1)[1]
                id_to_name[id] = name
                name_to_instr_self[name] = 0
            else:
                name = id_to_name[id]
            continue

        matches = re.findall(pattern_callee, line, re.MULTILINE)
        if len(matches) > 0:
            in_callee_function = True
            id_callee = re.split("[()]", matches[0])[1]
            if id_callee not in id_to_name:
                name_callee = matches[0].split(" ", 1)[1]
                id_to_name[id_callee] = name_callee
                name_to_instr_self[name_callee] = 0
            continue
        if in_a_function:
            numbers = re.finditer("^((([+-]?[0-9]+)|([*])) ([0-9])+)$", line)
            for number in numbers:
                # skip fist line in callee description
                if in_callee_function:
                    in_callee_function = False
                    continue

                num = number.group(0).split(" ")[1]
                name_to_instr_self[name] += int(num)

    name_to_instr_self = {
        key: val for key, val in name_to_instr_self.items() if val != 0
    }
    return name_to_instr_self


def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("-f", "--file", help="callgrind output file")
    args = vars(parser.parse_args())
    output = parse(fileinput.input(files=args["file"]))
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
