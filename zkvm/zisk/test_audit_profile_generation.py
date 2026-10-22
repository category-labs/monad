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

"""Exercise CMake's profile serialization and force-include configuration."""

import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


GUEST = Path(__file__).resolve().parents[1] / "guest"
TEMPLATES = ("dev-profile.json.in", "official-profile.json.in")


class ProfileGenerationTests(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory(prefix="monad-profile-")
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / "checkout with spaces"
        self.root.mkdir()

    def run_cmake(self, *args):
        result = subprocess.run(
            ["cmake", *map(str, args)], capture_output=True, text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def generate(self, template, value):
        text = (GUEST / template).read_text()
        variables = set(re.findall(r"@([A-Za-z0-9_]+)@", text))
        script = self.root / "generate.cmake"
        script.write_text(
            f'include("{GUEST}/configure_json.cmake")\n'
            + "".join(f"set({name} [==[{value}]==])\n" for name in sorted(variables))
            + f'configure_file("{GUEST / template}" "{self.root}/plain.json" @ONLY)\n'
            + f'monad_zkvm_configure_json("{GUEST / template}" "{self.root}/profile.json")\n'
            + f'file(WRITE "{self.root}/flags.txt" "${{CMAKE_CXX_FLAGS}}")\n'
        )
        self.run_cmake("-P", script)
        # Serialization must not change the actual compiler/signature inputs.
        self.assertEqual((self.root / "flags.txt").read_bytes(), value.encode())
        return text, variables, (self.root / "profile.json").read_text()

    def test_strings_round_trip_through_both_profiles(self):
        value = '-DNAME="value" -I"/path with spaces" \\literal; é '
        value += "".join(chr(code) for code in range(1, 32))
        for template in TEMPLATES:
            with self.subTest(template=template):
                text, variables, output = self.generate(template, value)
                expected = json.loads(text)
                for key, item in expected.items():
                    if isinstance(item, str) and item in {f"@{name}@" for name in variables}:
                        expected[key] = value
                self.assertEqual(json.loads(output), expected)

    def test_plain_values_keep_the_existing_json(self):
        for template in TEMPLATES:
            with self.subTest(template=template):
                _, _, output = self.generate(template, "plain-value")
                self.assertEqual(output, (self.root / "plain.json").read_text())

    def test_force_include_from_checkout_with_spaces(self):
        # Use the guest's actual option and header with a small native build.
        source = (GUEST / "CMakeLists.txt").read_text()
        option = re.search(
            r'string\(APPEND CMAKE_CXX_FLAGS\s+" -include [^\n]+\)', source,
        )
        self.assertIsNotNone(option)
        shutil.copy2(GUEST / "nodelete.hpp", self.root)
        (self.root / "probe.cpp").write_text("std::size_t probe() { return 0; }\n")
        (self.root / "CMakeLists.txt").write_text(
            "cmake_minimum_required(VERSION 3.20)\n"
            "project(profile_probe LANGUAGES CXX)\n"
            + option.group() + "\n"
            + "add_library(probe OBJECT probe.cpp)\n"
        )
        self.run_cmake("-S", self.root, "-B", self.root / "build")
        self.run_cmake("--build", self.root / "build")


if __name__ == "__main__":
    unittest.main()
