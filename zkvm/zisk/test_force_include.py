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

"""Check that the allocator declarations work in a checkout with spaces."""

from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest


GUEST = Path(__file__).resolve().parents[1] / "guest"


class ForceIncludeTests(unittest.TestCase):
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
