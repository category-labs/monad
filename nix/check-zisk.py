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

"""Check allocator assumptions and the reference ELF produced by Nix.

Toolchain versions, flags and dependencies belong to the Nix/CMake recipe.
These checks catch code drift; they do not prove guest correctness.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import subprocess


def strip_comments(src: str) -> str:
    """Remove C/C++ comments before inspecting function bodies."""
    out, i, n = [], 0, len(src)
    while i < n:
        if src.startswith("//", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        elif src.startswith("/*", i):
            j = src.find("*/", i + 2)
            out.append(" ")
            i = n if j < 0 else j + 2
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def delete_overloads(src: str) -> dict[str, str | None]:
    """Map delete signatures to bodies, or None for declarations.

    Normalise parameter names and whitespace before matching overloads.
    """
    src = strip_comments(src)
    found: dict[str, str | None] = {}
    for m in re.finditer(r"operator\s+delete\s*(\[\s*\])?\s*\(", src):
        array = "[]" if m.group(1) else ""
        depth, i, n = 1, m.end(), len(src)
        while i < n and depth:
            depth += (src[i] == "(") - (src[i] == ")")
            i += 1
        if depth:
            fail("unbalanced parameter list after an operator delete")
        params = []
        for p in src[m.end() : i - 1].split(","):
            p = p.strip()
            if not p:
                continue
            # Strip trailing parameter names, preserving types such as size_t.
            p = re.sub(r"(?<=[*&])\s*[A-Za-z_]\w*\s*$", "", p)
            p = re.sub(r"\s+[A-Za-z_]\w*\s*$", "", p)
            params.append(re.sub(r"\s+", "", p))
        key = f"operator delete{array}({','.join(params)})"
        rest = src[i:]
        j = re.match(r"\s*(noexcept\s*)?", rest).end()
        if j < len(rest) and rest[j] == "{":
            depth, k = 1, j + 1
            while k < len(rest) and depth:
                depth += (rest[k] == "{") - (rest[k] == "}")
                k += 1
            if depth:
                fail(f"unbalanced body for {key}")
            found[key] = rest[j + 1 : k - 1]
        else:
            found.setdefault(key, None)
    return found


def fail(message):
    raise ValueError(message)


# The replaceable deallocation functions the guest must define itself: it
# links without libstdc++, and the bump allocator never frees.
REQUIRED_DELETES = (
    "operator delete(void*)",
    "operator delete[](void*)",
    "operator delete(void*,std::size_t)",
    "operator delete[](void*,std::size_t)",
)


def check_allocator(repo):
    """The guest never deallocates: every delete and free must be a no-op.

    Link-time optimization inlines these bodies into their callers, so a
    body added here would run at every delete in the guest.
    """
    libstdcxx = (repo / "zkvm" / "core" / "libstdcxx.cpp").read_text(
        errors="replace"
    )
    # Discover overloads so new ones are checked too.
    defined = delete_overloads(libstdcxx)
    for key, body in sorted(defined.items()):
        if body is not None and body.strip():
            fail(f"libstdcxx.cpp defines {key} with a body; the family does nothing")
    for key in REQUIRED_DELETES:
        if key not in defined or defined[key] is None:
            fail(f"libstdcxx.cpp does not define {key}")
    libc = strip_comments(
        (repo / "zkvm" / "core" / "libc.cpp").read_text(errors="replace")
    )
    free_body = re.search(r"void free\(void \*(\w+)\)\s*\{(.*?)\n\}", libc, re.S)
    if free_body is None or free_body.group(2).split() != [
        f"(void){free_body.group(1)};"
    ]:
        fail("libc.cpp no longer defines free as a no-op")


def check_return(disassembly):
    # Check the encoding, not just the size: ebreak is also four bytes.
    instructions = re.findall(r"^\s*[0-9a-f]+:\s+([0-9a-f]+)\s", disassembly, re.M)
    if instructions != ["00008067"]:  # jalr x0, 0(ra), i.e. ret
        fail("expected a single RISC-V ret instruction")


def check_jumpdest(disassembly):
    if not re.search(r"\bcsrs\s+0x81c,", disassembly):
        fail("ELF does not contain the ZisK JUMPDEST syscall")


BRANCHES = {
    "beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez",
    "blez", "bgez", "bltz", "bgtz", "bgt", "ble", "bgtu", "bleu",
}
FUNCTION = re.compile(r"^([0-9a-f]+) <(.+)>:$")
INSTRUCTION = re.compile(r"^\s+([0-9a-f]+):\s+([0-9a-f]{4,8})\s+(\S+)(?:\s+(.*))?$")
MANUAL_JUMP = re.compile(r"monad_vm_manual_jump_(prefix|lag)_\d+$")
STACK_SLOT = re.compile(r"^(-?(?:0x[0-9a-f]+|\d+))\(sp\)$")
CALLEE_SAVED = {f"s{n}" for n in range(12)}
# Instructions whose first operand is not a destination register.
NO_DESTINATION = BRANCHES | {
    "sd", "sw", "sh", "sb", "j", "jr", "ret", "unimp", "nop", "fence",
    "ecall", "ebreak", "csrs", "csrc", "csrw", "csrsi", "csrci", "csrwi",
}


def check_hand_made_jumps(disassembly: str, marked_jumps, function_sizes=None, *, on_violation=None) -> int:
    """Check marked tail jumps for open frames and unrestored saved registers.

    Prefix and lag dispatch mark their own jalr. GCC does not insert a
    tail-call epilogue for these instructions. Follow branches, merging all incoming states: sp must
    return to its entry value and s0-s11 must retain their caller's values.
    Recognize restores only from matching stack saves. This is a code-drift
    check for the emitted instruction patterns, not a general ABI proof.
    The policy generator supplies on_violation to collect all unsafe handlers;
    the reference build fails on the first violation.
    """
    if not marked_jumps:
        fail("ELF has no manual jump markers")
    function_sizes = function_sizes or {}
    functions: dict[str, list[tuple[int, str, str, bool]]] = {}
    function_end = None
    current = None
    noreturn_calls = set()
    for line in disassembly.splitlines():
        header = FUNCTION.match(line)
        if header:
            name = header.group(2)
            if not name.startswith(".L") and not MANUAL_JUMP.fullmatch(name):
                size = function_sizes.get(name)
                function_end = (
                    int(header.group(1), 16) + size
                    if size is not None else None
                )
                current = (
                    functions.setdefault(name, [])
                    if name.startswith(("monad_vm_slot_", "_ZN5monad2vm11interpreter"))
                    else None
                )
            continue
        instruction = INSTRUCTION.match(line)
        if instruction and current is not None:
            address = int(instruction.group(1), 16)
            if function_end is not None and address >= function_end:
                continue
            # These runtime functions are declared [[noreturn]]. Do not
            # invent a fallthrough into the next error path after their call.
            encoding = int(instruction.group(2), 16)
            mnemonic = instruction.group(3)
            operands = instruction.group(4) or ""
            if mnemonic in ("jal", "jalr") and any(
                symbol in operands for symbol in (
                    "<_ZN5monad2vm7runtime7Context4exit",
                    "<_ZN5monad2vm7runtime12selfdestruct",
                )
            ):
                noreturn_calls.add(address)
            # jalr x0, imm(rs1), including the zero-offset jr alias.
            tail_jump = encoding & 0x7fff == 0x67
            if address in marked_jumps and not tail_jump:
                fail(f"manual jump marker at {address:x} does not label jalr x0")
            current.append((address, mnemonic, operands.split("#", 1)[0].strip(), tail_jump))

    checked_jumps = set()
    for name, instructions in functions.items():
        if not any(ins[0] in marked_jumps for ins in instructions):
            continue
        index = {ins[0]: i for i, ins in enumerate(instructions)}
        # State: sp relative to entry (None if unknown), modified registers,
        # and stack locations known to hold original callee-saved values.
        states = {instructions[0][0]: (0, frozenset(), frozenset())}
        pending = [instructions[0][0]]
        while pending:
            address = pending.pop()
            position = index[address]
            _, mnemonic, operands, tail_jump = instructions[position]
            stack_offset, modified, saved = states[address]
            saved = dict(saved)
            parts = [part.strip() for part in operands.split(",")]
            destination = parts[0] if parts else ""
            if destination == "fp":
                destination = "s0"
            stack_slot = STACK_SLOT.fullmatch(parts[1]) if len(parts) == 2 else None
            slot = (stack_offset + int(stack_slot.group(1), 0)
                    if stack_slot and stack_offset is not None else None)
            if mnemonic in ("sd", "sw", "sh", "sb") and slot is not None:
                width = {"sd": 8, "sw": 4, "sh": 2, "sb": 1}[mnemonic]
                saved = {at: reg for at, reg in saved.items()
                         if at + 8 <= slot or slot + width <= at}
                if (mnemonic == "sd" and destination in CALLEE_SAVED
                        and destination not in modified):
                    saved[slot] = destination
            if mnemonic not in NO_DESTINATION and destination in CALLEE_SAVED:
                if (mnemonic == "ld" and slot is not None
                        and saved.get(slot) == destination):
                    modified = modified - {destination}
                else:
                    modified = modified | {destination}
            if mnemonic not in NO_DESTINATION and destination == "sp":
                if (mnemonic == "addi" and len(parts) == 3
                        and parts[1] == "sp" and stack_offset is not None):
                    stack_offset += int(parts[2], 0)
                else:
                    stack_offset = None
                    saved = {}
            following = (instructions[position + 1][0]
                         if position + 1 < len(instructions) else None)
            if address in marked_jumps:
                checked_jumps.add(address)
                if stack_offset != 0 or modified:
                    reason = ("with its frame open or unknown" if stack_offset != 0
                              else f"with {', '.join(sorted(modified))} written and not restored")
                    message = f"{name} takes a manual jump at {address:x} {reason}"
                    if on_violation is None:
                        fail(message)
                    on_violation(name, message)
            if address in noreturn_calls:
                successors = []
            elif mnemonic == "j":
                successors = [int(operands.split()[0], 16)]
            elif mnemonic in BRANCHES:
                successors = [int(parts[-1].split()[0], 16), following]
            elif mnemonic in ("jr", "ret", "unimp") or tail_jump:
                successors = []
            else:
                successors = [following]
            outgoing = (stack_offset, frozenset(modified), frozenset(saved.items()))
            for successor in successors:
                if successor not in index:
                    continue
                merged = outgoing
                if successor in states:
                    old_stack, old_modified, old_saved = states[successor]
                    merged = (stack_offset if old_stack == stack_offset else None,
                              old_modified | outgoing[1], old_saved & outgoing[2])
                if states.get(successor) != merged:
                    states[successor] = merged
                    pending.append(successor)
    missing = marked_jumps - checked_jumps
    if missing:
        fail(f"{len(missing)} unchecked manual jump marker(s), first at {min(missing):x}")
    return len(checked_jumps)


def manual_jump_addresses(symbols):
    # Local assembly labels have an address but need not have a symbol size.
    sites = set()
    families = set()
    for line in symbols.splitlines():
        fields = line.split()
        if fields and (match := MANUAL_JUMP.fullmatch(fields[-1])):
            sites.add(int(fields[0], 16))
            families.add(match[1])
    if families != {"prefix", "lag"}:
        fail("ELF is missing manual jump markers for prefix or lag dispatch")
    return sites


def parse_function_sizes(symbols):
    return {fields[3]: int(fields[1], 16) for line in symbols.splitlines()
            if len(fields := line.split()) == 4 and fields[2] in ("t", "T")}


def check_elf(elf, commit, prefix, build_id="none"):
    marker = b"monad-zkvm;commit=" + commit.encode() + b";build=" + build_id.encode() + b"\0"
    if not re.fullmatch(r"[0-9a-f]{40}", commit) or marker not in elf.read_bytes():
        fail("ELF does not contain the expected commit marker")

    def tool(name, *args):
        return subprocess.check_output([prefix + name, *args, str(elf)], text=True)

    disassembly = tool("objdump", "-d")
    check_jumpdest(disassembly)
    attributes = tool("readelf", "-A")
    for extension in ("zba", "zbb", "zbs", "zbkb"):
        if not re.search(r"_" + extension + r"[0-9]", attributes):
            fail(f"ELF attributes omit {extension}")
    symbols = tool("nm", "--print-size", "--defined-only")
    manual_jumps = check_hand_made_jumps(
        disassembly, manual_jump_addresses(symbols), parse_function_sizes(symbols))
    for line in symbols.splitlines():
        fields = line.split()
        if len(fields) == 4 and (
            fields[3].startswith(("_Zdl", "_Zda")) or fields[3] == "free"
        ):
            address, size = int(fields[0], 16), int(fields[1], 16)
            if size != 4:
                fail(f"{fields[3]} is not a bare return ({size} bytes)")
            # Use addresses so aliased symbol names are checked too.
            check_return(tool(
                "objdump", "-d", f"--start-address={address}",
                f"--stop-address={address + size}",
            ))

    return manual_jumps


def cache_values(path):
    values = {}
    for line in path.read_text().splitlines():
        match = re.match(r"([^:#/][^:]*):[^=]+=(.*)", line)
        if match:
            values[match[1]] = match[2]
    return values


def check_dirty_accounts(build_dir: Path, repo: Path) -> None:
    option = "MONAD_ZKVM_NO_DIRTY_ACCOUNTS"
    if cache_values(build_dir / "CMakeCache.txt").get(option) != "ON":
        fail(f"matching CMake cache did not enable {option}")
    database = build_dir / "compile_commands.json"
    if not database.is_file():
        fail("compile_commands.json is missing; reconfigure the official build")
    commands = json.loads(database.read_text())
    required = {
        (repo / "category/execution/ethereum/state3/state.cpp").resolve(),
        (repo / "zkvm/guest/execute_witness.cpp").resolve(),
    }
    tracer = (repo / "category/execution/ethereum/trace/state_tracer.cpp").resolve()
    seen = set()
    for entry in commands:
        source = (Path(entry["directory"]) / entry["file"]).resolve()
        if source == tracer:
            fail("state_tracer.cpp is compiled despite disabled dirty-account lists")
        if source not in required:
            continue
        args = entry.get("arguments")
        if args is None:
            args = shlex.split(entry["command"])
        # Respect later -D/-U overrides, including their separated spellings.
        enabled = False
        tokens = iter(args)
        for arg in tokens:
            if arg in ("-D", "-U"):
                arg += next(tokens, "")
            if arg == "-U" + option:
                enabled = False
            elif arg.startswith("-D"):
                name, _, value = arg[2:].partition("=")
                if name == option:
                    enabled = value in ("", "1")
        if not enabled:
            fail(f"{source.name} compile command does not enable {option}")
        seen.add(source)
    if seen != required:
        fail("compile commands are missing State or the guest entry point")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path)
    parser.add_argument("--elf", type=Path)
    parser.add_argument("--binutils-prefix")
    parser.add_argument("--inputs", type=Path)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--build-id", default="none")
    parser.add_argument("--build-dir", type=Path)
    args = parser.parse_args()
    if any((args.elf, args.binutils_prefix, args.inputs, args.manifest)) and not all(
        (args.elf, args.binutils_prefix, args.inputs, args.manifest)
    ):
        parser.error("ELF checking requires --elf, --binutils-prefix, --inputs and --manifest")
    try:
        check_allocator(args.repo)
        if args.build_dir:
            check_dirty_accounts(args.build_dir, args.repo)
        if args.elf:
            inputs = json.loads(args.inputs.read_text())
            inputs["interpreter_manual_jumps"] = check_elf(
                args.elf, inputs["commit"], args.binutils_prefix, args.build_id
            )
            inputs["build"] = args.build_id
            inputs["elf_sha256"] = hashlib.sha256(args.elf.read_bytes()).hexdigest()
            args.manifest.write_text(json.dumps(inputs, indent=2, sort_keys=True) + "\n")
    except ValueError as error:
        parser.exit(1, f"ZisK build check failed: {error}\n")


if __name__ == "__main__":
    main()
