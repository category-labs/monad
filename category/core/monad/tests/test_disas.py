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

import os
import re
from glob import glob
from os import path
from subprocess import check_output

THIS_FILE = path.realpath(__file__)
THIS_DIR = path.dirname(THIS_FILE)
TEST_DIR = path.join(THIS_DIR, "disas")

TARGET_REGEX = "((?:call|ja|jae|jb|jbe|je|jmp|jne|js)[ ]+)0x[0-9a-f]+[ ]+"
TARGET_PATTERN = re.compile(TARGET_REGEX)

CC = os.getenv("CC")
assert CC

def _get_test_ids(test_dir):
    test_ids = []
    files = glob("**/*.py", root_dir=test_dir, recursive=True)
    for file in files:
        if file.startswith("_"):
            continue
        test_id = file[0:-3]
        test_ids.append(test_id)
    return test_ids

class DisassemblyTestCase:
    def __init__(self, test_id):
        test_file = path.join(TEST_DIR, "%s.py" % (test_id,))
        ns = {}
        with open(test_file, "r") as f:
            code = compile(f.read(), test_file, "exec")
            exec(code, ns, ns)

        compilers = ns.get("compilers")
        obj = ns.get("obj")
        syms = ns.get("syms")

        assert isinstance(compilers, list)
        for compiler in compilers:
            assert isinstance(compiler, str)
        assert isinstance(obj, str)
        assert isinstance(syms, list)
        for sym in syms:
            assert isinstance(sym, str)

        self.test_id = test_id
        self.compilers = compilers
        self.obj = obj
        self.syms = syms
        self.matching_compiler = None

    def find_matching_compiler(self):
        if not self.matching_compiler:
            for c in self.compilers:
                if CC.startswith(c):
                    self.matching_compiler = c
        return self.matching_compiler

    def _gen_result(self):
        obj = path.join("**", self.obj)
        objs = glob(obj, recursive=True)
        assert len(objs) == 1
        obj = objs[0]
        cmd = [
            "gdb",
            "-batch",
            "-ex",
            "file %s" % (obj,),
        ]
        for sym in self.syms:
            cmd += [
                "-ex",
                "disas '%s'" % (sym,),
            ]
        result = check_output(cmd)
        result = result.decode("ascii")
        result = result.splitlines()

        def remove_address(line: str):
            line = line.expandtabs()
            if not line.startswith("   0x"):
                return line
            line = line[22:]
            assert line[0] == "<"
            return line

        result = [remove_address(line) for line in result]

        def remove_target(line: str):
            return TARGET_PATTERN.sub("\\1", line, count=1)

        result = [remove_target(line) for line in result]

        def gdb_10_to_12(line: str):  # TODO
            return line.replace("nopw   %cs:0", "cs nopw 0")

        result = [gdb_10_to_12(line) for line in result]
        result = "\n".join(result)
        return result

    def _gen_result_objdump(self):
        compiler = self.find_matching_compiler()

        obj = path.join("**", self.obj)
        objs = glob(obj, recursive=True)
        assert len(objs) == 1
        obj = objs[0]
        cmd = [
            "objdump",
            "--demangle",
            "--disassemble",
            "--reloc",
            "--insn-width=8",
            obj,
        ]
        result = check_output(cmd)
        result = result.decode("ascii")
        result = result.splitlines()

        result2 = []
        match = False
        for line in result:
            if not match:
                for sym in self.syms:
                    if "<%s>:" % (sym,) in line:
                        match = True
                        break
            if match:
                result2.append(line)
                if not line.strip():
                    match = False

        result = "\n".join(result2)
        return result

    def _load_result(self):
        compiler = self.find_matching_compiler()
        result_file = path.join(TEST_DIR, "%s_%s.dis" % (self.test_id, compiler))
        with open(result_file, "r") as f:
            result = f.read()
        return result

    def save_result(self):
        compiler = self.find_matching_compiler()
        result = self._gen_result_objdump()
        result_file = path.join(TEST_DIR, "%s_%s.dis" % (self.test_id, compiler))
        with open(result_file, "w") as f:
            f.write(result)

    def run(self):
        print(self.test_id)
        expected_result = self._load_result()
        current_result = self._gen_result_objdump()
        assert expected_result == current_result

def _create_test_class(test_dir):
    class TestDisas:
        pass

    test_ids = _get_test_ids(test_dir)
    test_cases = [ DisassemblyTestCase(test_id) for test_id in test_ids ]
    test_cases = [
        test_case
        for test_case in test_cases
        if test_case.find_matching_compiler()
    ]
    for test_case in test_cases:
        def test_func(self, test_case=test_case):
            test_case.run()

        setattr(TestDisas, "test_%s" % (test_case.test_id,), test_func)

    setattr(TestDisas, "test_ids", test_ids)
    setattr(TestDisas, "test_cases", test_cases)

    return TestDisas


TestDisas = _create_test_class(TEST_DIR)

def main():
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("cmd", choices=("generate",))
    args = parser.parse_args()
    if args.cmd == "generate":
        for test_case in TestDisas.test_cases:
            test_case.save_result()


if __name__ == "__main__":
    main()
