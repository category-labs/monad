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

#!/usr/bin/env python3
"""
NOTE: This script was developed using Copilot's agent mode AI.

Script to check for overlapping macro usages in explicit_traits.hpp.

This script finds usages of all explicit trait instantiation macros:
- EXPLICIT_EVM_TRAITS, EXPLICIT_MONAD_TRAITS, EXPLICIT_TRAITS (functions)
- EXPLICIT_EVM_TRAITS_CLASS, EXPLICIT_MONAD_TRAITS_CLASS, EXPLICIT_TRAITS_CLASS (classes)
- EXPLICIT_EVM_TRAITS_MEMBER, EXPLICIT_MONAD_TRAITS_MEMBER, EXPLICIT_TRAITS_MEMBER (members)

It checks for overlaps according to these rules:

1. Use of `EXPLICIT_EVM_TRAITS*` in one TU and either `EXPLICIT_MONAD_TRAITS*`
   or `EXPLICIT_EVM_TRAITS*` in another TU (with the same argument to the macro) is an overlap.
2. Duplicated uses of the same macro with the same argument in the same file is an overlap.
3. It's explicitly OK to use `EXPLICIT_MONAD_TRAITS*` and `EXPLICIT_EVM_TRAITS*`
   with the same argument in different TUs.

Additionally, the script enforces that these macros should ONLY be used in .cpp files.
Any usage in header files (.hpp) is treated as an error.

Usage:
    python3 check-trait-instantiations.py [root_directory]

If no directory is specified, defaults to the parent directory of the script.
"""

import os
import re
import sys
from collections import defaultdict
from typing import Dict, List, Set, Tuple, NamedTuple


class MacroUsage(NamedTuple):
    """Represents a macro usage."""

    file_path: str
    line_number: int
    macro_name: str
    argument: str


def check_header_file(file_path: str, pattern: re.Pattern, root_path: str) -> None:
    """Check a header file for macro usages and error if any are found."""
    with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
        content = f.read()

    for match in pattern.finditer(content):
        argument = match.group(2).strip()

        # Skip macro definitions (single letter arguments like 'f' or 'c')
        if len(argument) == 1 and argument.isalpha():
            continue

        # Skip if this looks like a macro definition context
        line_start = content.rfind("\n", 0, match.start()) + 1
        line_end = content.find("\n", match.end())
        if line_end == -1:
            line_end = len(content)
        line_content = content[line_start:line_end]
        if line_content.strip().startswith("#define"):
            continue

        # If we get here, it's a real usage in a header file - error!
        line_number = content[: match.start()].count("\n") + 1
        rel_path = get_relative_path(file_path, root_path)
        print(
            f"❌ ERROR: Explicit trait macro found in header file {rel_path}:{line_number}",
            file=sys.stderr,
        )
        print(
            "   These macros should only be used in .cpp files",
            file=sys.stderr,
        )
        sys.exit(1)


def process_cpp_file(file_path: str, pattern: re.Pattern) -> List[MacroUsage]:
    """Process a .cpp file and return any macro usages found."""
    usages: List[MacroUsage] = []

    with open(file_path, "r", encoding="utf-8", errors="ignore") as f:
        content = f.read()

    for match in pattern.finditer(content):
        macro_name = match.group(1)
        argument = match.group(2).strip()
        line_number = content[: match.start()].count("\n") + 1

        usages.append(
            MacroUsage(
                file_path=file_path,
                line_number=line_number,
                macro_name=macro_name,
                argument=argument,
            )
        )

    return usages


def find_macro_usages(root_path: str) -> List[MacroUsage]:
    """Find all usages of the explicit traits macros in the codebase."""
    usages: List[MacroUsage] = []

    # Pattern to match the macro calls (function, class, and member versions)
    # This pattern ensures we don't match macro definitions by requiring the argument
    # to not be a single letter (which would indicate a macro parameter like 'f' or 'c')
    pattern = re.compile(
        r"^\s*(EXPLICIT_EVM_TRAITS(?:_CLASS|_MEMBER)?|EXPLICIT_MONAD_TRAITS(?:_CLASS|_MEMBER)?|EXPLICIT_TRAITS(?:_CLASS|_MEMBER)?)\s*\(\s*([^)]+)\s*\)",
        re.MULTILINE,
    )

    for root, dirs, files in os.walk(root_path):
        # Skip build directories and third_party
        dirs[:] = [
            d for d in dirs if not d.startswith(("build", "third_party", ".git"))
        ]

        for file in files:
            file_path = os.path.join(root, file)

            if file.endswith(".hpp"):
                check_header_file(file_path, pattern, root_path)

            elif file.endswith(".cpp"):
                file_usages = process_cpp_file(file_path, pattern)
                usages.extend(file_usages)

    return usages


def get_relative_path(file_path: str, root_path: str) -> str:
    """Get relative path from root."""
    try:
        return os.path.relpath(file_path, root_path)
    except ValueError:
        return file_path


def check_overlaps(
    usages: List[MacroUsage], root_path: str, verbose: bool = False
) -> List[str]:
    """Check for overlaps according to the specified rules."""
    errors = []

    # Group usages by argument
    by_argument: Dict[str, List[MacroUsage]] = defaultdict(list)
    for usage in usages:
        by_argument[usage.argument].append(usage)

    # Group usages by (file, macro, argument) to detect duplicates
    seen_combinations: Set[Tuple[str, str, str]] = set()

    for usage in usages:
        combination = (usage.file_path, usage.macro_name, usage.argument)
        if combination in seen_combinations:
            # Rule 2: Duplicated uses of the same macro with the same argument
            rel_path = get_relative_path(usage.file_path, root_path)
            errors.append(
                f"DUPLICATE: {usage.macro_name}({usage.argument}) "
                f"appears multiple times in {rel_path}"
            )
        else:
            seen_combinations.add(combination)

    # Check each argument for overlaps
    for argument, arg_usages in by_argument.items():
        if len(arg_usages) <= 1:
            continue

        # Group by file
        by_file: Dict[str, List[MacroUsage]] = defaultdict(list)
        for usage in arg_usages:
            by_file[usage.file_path].append(usage)

        if len(by_file) <= 1:
            continue  # All usages in same file, no cross-TU overlap

        # Check for Rule 1: EXPLICIT_EVM_TRAITS in one TU and
        # (EXPLICIT_MONAD_TRAITS or EXPLICIT_EVM_TRAITS) in another TU
        files_with_evm = set()
        files_with_monad = set()

        for file_path, file_usages in by_file.items():
            has_evm = any(
                u.macro_name
                in (
                    "EXPLICIT_EVM_TRAITS",
                    "EXPLICIT_EVM_TRAITS_CLASS",
                    "EXPLICIT_EVM_TRAITS_MEMBER",
                    "EXPLICIT_TRAITS",
                    "EXPLICIT_TRAITS_CLASS",
                    "EXPLICIT_TRAITS_MEMBER",
                )
                for u in file_usages
            )
            has_monad = any(
                u.macro_name
                in (
                    "EXPLICIT_MONAD_TRAITS",
                    "EXPLICIT_MONAD_TRAITS_CLASS",
                    "EXPLICIT_MONAD_TRAITS_MEMBER",
                    "EXPLICIT_TRAITS",
                    "EXPLICIT_TRAITS_CLASS",
                    "EXPLICIT_TRAITS_MEMBER",
                )
                for u in file_usages
            )

            if has_evm:
                files_with_evm.add(file_path)
            if has_monad:
                files_with_monad.add(file_path)

        # Check if EXPLICIT_EVM_TRAITS (or EXPLICIT_TRAITS) is used in multiple files
        # This violates Rule 1
        if len(files_with_evm) > 1:
            rel_paths = [get_relative_path(f, root_path) for f in files_with_evm]
            errors.append(
                f"OVERLAP: {argument} has EVM traits instantiated in multiple TUs: "
                f"{', '.join(rel_paths)}"
            )

        # Check if EXPLICIT_MONAD_TRAITS (or EXPLICIT_TRAITS) is used in multiple files
        # This also violates Rule 1
        if len(files_with_monad) > 1:
            rel_paths = [get_relative_path(f, root_path) for f in files_with_monad]
            errors.append(
                f"OVERLAP: {argument} has Monad traits instantiated in multiple TUs: "
                f"{', '.join(rel_paths)}"
            )

    return errors


def main():
    """Main function."""
    import argparse

    parser = argparse.ArgumentParser(
        description="Check for overlapping trait instantiation macro usages"
    )
    parser.add_argument(
        "root_path",
        nargs="?",
        help="Root directory to search (defaults to parent of script directory)",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Show detailed information about overlap detection",
    )

    args = parser.parse_args()

    if args.root_path:
        root_path = args.root_path
    else:
        # Default to the monad repository root
        script_dir = os.path.dirname(os.path.abspath(__file__))
        root_path = os.path.dirname(script_dir)

    if not os.path.isdir(root_path):
        print(f"Error: {root_path} is not a valid directory", file=sys.stderr)
        sys.exit(1)

    print(f"Checking trait instantiations in: {root_path}")
    print()

    # Find all macro usages
    usages = find_macro_usages(root_path)

    if not usages:
        print("No macro usages found.")
        return

    print(f"Found {len(usages)} macro usages:")

    # Group and display usages
    by_argument: Dict[str, List[MacroUsage]] = defaultdict(list)
    for usage in usages:
        by_argument[usage.argument].append(usage)

    for argument in sorted(by_argument.keys()):
        print(f"\n{argument}:")
        for usage in sorted(
            by_argument[argument], key=lambda x: (x.file_path, x.line_number)
        ):
            rel_path = get_relative_path(usage.file_path, root_path)
            print(f"  {usage.macro_name} in {rel_path}:{usage.line_number}")

    # Check for overlaps
    errors = check_overlaps(usages, root_path, args.verbose)

    if errors:
        print(f"\n{'=' * 60}")
        print("ERRORS FOUND:")
        print("=" * 60)
        for error in sorted(errors):
            print(f"❌ {error}")
        print(f"\nFound {len(errors)} error(s).")
        sys.exit(1)
    else:
        print(f"\n{'=' * 60}")
        print("✅ No overlaps found! All macro usages are valid.")
        print("=" * 60)


if __name__ == "__main__":
    main()
