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

"""Allocator assumptions and linked-code checks for the reference build."""

import importlib.util
from pathlib import Path
import runpy
import shutil
import os
import subprocess
import json
import sys
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location("check_zisk", Path(__file__).with_name("check-zisk.py"))
check = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check)
REPO = Path(__file__).resolve().parent.parent


class ZiskChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        for name in ("zkvm/core/libstdcxx.cpp", "zkvm/core/libc.cpp"):
            dest = self.repo / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(REPO / name, dest)

    def test_current_allocator(self):
        check.check_allocator(self.repo)

    def test_delete_body_is_checked_even_when_absent_from_elf(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        p.write_text(p.read_text().replace("noexcept {}", "noexcept { abort(); }", 1))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_new_overload_cannot_hide_a_body(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        with p.open("a") as f:
            f.write("void operator delete(void *p, std::align_val_t) noexcept { abort(); }\n")
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_missing_definition_is_rejected(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        p.write_text(p.read_text().replace("void operator delete(void *) noexcept {}", ""))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_comment_cannot_supply_a_definition(self):
        p = self.repo / "zkvm/core/libstdcxx.cpp"
        p.write_text(p.read_text().replace("void operator delete(void *) noexcept {}", "// void operator delete(void *) noexcept {}"))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_free_body_is_checked(self):
        p = self.repo / "zkvm/core/libc.cpp"
        p.write_text(p.read_text().replace("(void)ptr;", "(void)ptr; abort();"))
        with self.assertRaises(ValueError):
            check.check_allocator(self.repo)

    def test_jumpdest_is_required(self):
        check.check_jumpdest("80000010: 81c52073 csrs 0x81c,a0\n")
        with self.assertRaises(ValueError):
            check.check_jumpdest("80000010: 00000013 nop\n")

    def test_ret_encoding(self):
        check.check_return("80000000: 00008067 ret\n")
        for code in ("80000000: 00100073 ebreak\n", "", "80000000: 00008067 ret\n80000004: 00000013 nop\n"):
            with self.subTest(code=code), self.assertRaises(ValueError):
                check.check_return(code)

    def test_elf_checks_identity_isa_and_surviving_functions(self):
        elf = self.repo / "guest"
        commit = "a" * 40
        elf.write_bytes(b"monad-zkvm;commit=" + commit.encode() + b";build=none\0")
        with self.assertRaises(ValueError):
            check.check_elf(elf, commit, "riscv-", "another-build")
        attrs = 'Tag_RISCV_arch: "rv64i2p1_m2p0_a2p1_zba1p0_zbb1p0_zbs1p0_zbkb1p0"'
        jumpdest = "80000010: 81c52073 csrs 0x81c,a0\n"
        jumpdest += ("80000100 <monad_vm_slot_15_60>:\n"
                     " 80000100: 00050463 beqz a0,80000108\n"
                     "80000104 <monad_vm_manual_jump_lag_1>:\n"
                     " 80000104: 00078067 jr a5\n"
                     "80000108 <monad_vm_manual_jump_prefix_2>:\n"
                     " 80000108: fe078067 jr -32(a5)\n")
        nm = ("80000000 00000004 T free\n80000100 0000000c T monad_vm_slot_15_60\n"
              "80000104 t monad_vm_manual_jump_lag_1\n80000108 t monad_vm_manual_jump_prefix_2\n")
        with patch.object(check.subprocess, "check_output", side_effect=[jumpdest, attrs, nm, "80000000: 00008067 ret\n"]):
            check.check_elf(elf, commit, "riscv-")
        with self.assertRaises(ValueError):
            check.check_elf(elf, "b" * 40, "riscv-")
        with patch.object(check.subprocess, "check_output", side_effect=[jumpdest, attrs.replace("_zba1p0", "")]), self.assertRaises(ValueError):
            check.check_elf(elf, commit, "riscv-")
        with patch.object(check.subprocess, "check_output", side_effect=[jumpdest, attrs, nm, "80000000: 00100073 ebreak\n"]), self.assertRaises(ValueError):
            check.check_elf(elf, commit, "riscv-")


class DirtyAccountsChecks(unittest.TestCase):
    def test_effective_definitions_and_excluded_tracer(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "CMakeCache.txt").write_text(
                "MONAD_ZKVM_NO_DIRTY_ACCOUNTS:BOOL=ON\n"
            )
            sources = [
                "category/execution/ethereum/state3/state.cpp",
                "zkvm/guest/execute_witness.cpp",
            ]

            def commands(flags, tracer=False):
                entries = [
                    {"directory": tmp, "file": src, "arguments": ["g++", *flags]}
                    for src in sources
                ]
                if tracer:
                    entries.append({
                        "directory": tmp,
                        "file": "category/execution/ethereum/trace/state_tracer.cpp",
                        "arguments": [],
                    })
                (root / "compile_commands.json").write_text(json.dumps(entries))

            commands(["-DMONAD_ZKVM_NO_DIRTY_ACCOUNTS=1"])
            check.check_dirty_accounts(root, root)
            for flags in (
                ["-DMONAD_ZKVM_NO_DIRTY_ACCOUNTS", "-UMONAD_ZKVM_NO_DIRTY_ACCOUNTS"],
                ["-D", "MONAD_ZKVM_NO_DIRTY_ACCOUNTS=0"],
            ):
                commands(flags)
                with self.assertRaises(ValueError):
                    check.check_dirty_accounts(root, root)
            commands(["-DMONAD_ZKVM_NO_DIRTY_ACCOUNTS"], tracer=True)
            with self.assertRaises(ValueError):
                check.check_dirty_accounts(root, root)


class ManualJumpChecks(unittest.TestCase):
    @staticmethod
    def assembly(lines, name="monad_vm_slot_15_60", start=0x100):
        result = f"{start:08x} <{name}>:\n"
        for i, line in enumerate(lines):
            # The audit decodes opcode, funct3 and rd for tail jumps.
            word = "00078067" if line.startswith(("jr\t", "jalr\tzero,")) else "00000013"
            result += f" {start + 4*i:x}:\t{word}\t{line}\n"
        return result

    def audit(self, lines):
        return check.check_hand_made_jumps(
            self.assembly(lines), {0x100 + 4 * (len(lines) - 1)})

    def test_frameless_jumps(self):
        for jump in ("jr\t-32(a5)", "jr\t-56(a5)", "jalr\tzero,-32(a5)"):
            self.assertEqual(self.audit([jump]), 1)

    def test_collects_all_unsafe_handlers_without_weakening_normal_audit(self):
        code = self.assembly(["addi\tsp,sp,-16", "jr\t-32(a5)"])
        code += self.assembly(["li\ts0,42", "jr\t-56(a5)"], "monad_vm_slot_12_55_4", start=0x200)
        violations = set()
        check.check_hand_made_jumps(
            code, {0x104, 0x204}, on_violation=lambda name, reason: violations.add(name))
        self.assertEqual(violations, {"monad_vm_slot_15_60", "monad_vm_slot_12_55_4"})
        with self.assertRaises(ValueError):
            check.check_hand_made_jumps(code, {0x104, 0x204})

    def test_function_size_excludes_slot_padding(self):
        code = ["addi\tsp,sp,-16", "jal\t200 <noreturn_exit>",
                "nop", "jr\t-32(a5)"]
        with self.assertRaisesRegex(ValueError, "unchecked"):
            check.check_hand_made_jumps(
                self.assembly(code), {0x10c}, {"monad_vm_slot_15_60": 8})

    def test_noreturn_call_does_not_fall_through(self):
        code = ["beqz\ta0,110", "addi\tsp,sp,-16",
                "jal\t200 <_ZN5monad2vm7runtime7Context4exitENS1_10StatusCodeE>",
                "nop", "jr\t-32(a5)"]
        self.assertEqual(self.audit(code), 1)

    def test_open_or_unknown_stack(self):
        for instruction in ("addi\tsp,sp,-16", "mv\tsp,a0"):
            with self.assertRaisesRegex(ValueError, "frame open"):
                self.audit([instruction, "jr\t-32(a5)"])

    def test_saved_registers(self):
        for register in ("s0", "s11", "fp"):
            with self.assertRaisesRegex(ValueError, "not restored"):
                self.audit([f"mv\t{register},a0", "jr\t-32(a5)"])

    def test_matching_restore(self):
        code = ["addi\tsp,sp,-16", "sd\ts0,8(sp)", "mv\ts0,a0",
                "ld\ts0,8(sp)", "addi\tsp,sp,16", "jr\t-32(a5)"]
        self.assertEqual(self.audit(code), 1)

    def test_arbitrary_load_is_not_a_restore(self):
        for save in ("sd\ta0,8(sp)", "sd\ts1,8(sp)"):
            code = ["addi\tsp,sp,-16", save, "mv\ts0,a0", "ld\ts0,8(sp)",
                    "addi\tsp,sp,16", "jr\t-32(a5)"]
            with self.assertRaisesRegex(ValueError, "not restored"):
                self.audit(code)

    def test_overwritten_save(self):
        code = ["addi\tsp,sp,-16", "sd\ts0,8(sp)", "sb\ta0,9(sp)",
                "mv\ts0,a0", "ld\ts0,8(sp)", "addi\tsp,sp,16", "jr\t-32(a5)"]
        with self.assertRaisesRegex(ValueError, "not restored"):
            self.audit(code)

    def test_both_branch_paths_are_checked(self):
        # The fallthrough path reaches the join first and is safe; the other
        # path must still be processed after it, rather than silently skipped.
        for change, message in (("mv\ts0,a0", "not restored"),
                                ("addi\tsp,sp,-16", "frame open")):
            code = ["beqz\ta0,10c", "nop", "j\t110", change, "jr\t-32(a5)"]
            with self.assertRaisesRegex(ValueError, message):
                self.audit(code)

    def test_loop_converges_and_counts_once(self):
        code = ["addi\ta0,a0,-1", "bnez\ta0,100", "jr\t-32(a5)"]
        self.assertEqual(self.audit(code), 1)

    def test_unreachable_and_out_of_scope_code(self):
        code = ["j\t108", "addi\tsp,sp,-16", "jr\t-32(a5)"]
        self.assertEqual(self.audit(code), 1)
        with self.assertRaisesRegex(ValueError, "unchecked"):
            check.check_hand_made_jumps(self.assembly(code, "unrelated"), {0x108})

    def test_unmarked_compiler_jump_is_ignored(self):
        # One path jumps with an open frame via an unmarked nonzero offset.
        # The other reaches the marked register jump with its entry state.
        code = self.assembly(["beqz\ta0,10c", "addi\tsp,sp,-16", "jr\t-32(a5)", "jr\ta5"])
        self.assertEqual(check.check_hand_made_jumps(code, {0x10c}), 1)
        with self.assertRaisesRegex(ValueError, "frame open"):
            check.check_hand_made_jumps(code, {0x108, 0x10c})

    def test_swap1_pop_prefix_is_a_marked_lag_dispatch(self):
        symbols = ("100 t monad_vm_manual_jump_prefix_1\n"
                   "104 t monad_vm_manual_jump_lag_swap1_pop_15_6\n")
        self.assertEqual(check.manual_jump_addresses(symbols), {0x100, 0x104})

    def test_missing_marker_family_fails(self):
        with self.assertRaisesRegex(ValueError, "missing"):
            check.manual_jump_addresses("100 t monad_vm_manual_jump_lag_1")

    def test_invalid_or_missing_markers_fail(self):
        code = self.assembly(["nop", "jr\ta5"])
        for markers, error in ((set(), "no manual"), ({0x100}, "does not label"),
                               ({0x104, 0x108}, "unchecked")):
            with self.subTest(markers=markers), self.assertRaisesRegex(ValueError, error):
                check.check_hand_made_jumps(code, markers)


class FramePolicyGeneration(unittest.TestCase):
    tool = runpy.run_path(str(REPO / "nix/regenerate-frame-opcodes.py"))

    def test_reaudits_and_combines_the_two_deferred_configurations(self):
        names = {1: "ADD", 2: "MUL", 3: "SUB"}
        # SUB first appears in the eager probe, then also in production
        # after the compiler has seen the first round of exclusions.
        answers = iter([{1}, {2}, {3}, {3}, set(), set(), set(), set(), set()])
        observed = []

        def measure(mode, policy):
            observed.append((mode, policy))
            return next(answers)

        policy = self.tool["converge"](names, measure)
        self.assertEqual([mode for mode, _ in observed], list(self.tool["MODES"]) * 3)
        self.assertEqual([text for _, text in observed[-3:]], [policy] * 3)
        self.assertEqual(policy, self.tool["BANNER"] +
                         "case SUB:\n    return true;\n" +
                         "#if !defined(MONAD_ZKVM_GAS_CHECK_EVERY_OPCODE)\n" +
                         "case ADD:\ncase MUL:\n    return true;\n#endif\n")

    def test_refuses_an_unsafe_handler_already_excluded(self):
        with self.assertRaisesRegex(ValueError, "persists"):
            self.tool["converge"]({1: "ADD"}, lambda mode, policy: {1})


if __name__ == "__main__":
    unittest.main()
