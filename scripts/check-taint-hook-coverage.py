#!/usr/bin/env python3
"""Lint: every interpreter handler must route taint through the standard
dispatch (MONAD_VM_NEXT* macros -> taint_after_instruction) or carry explicit
taint handling, unless it is on the audited zero-stack-consumption allowlist.

Guards the taint system's deny-by-default against future opcodes whose
handlers use custom tails (the jump/jumpi/return/revert/selfdestruct seam):
a new handler that bypasses the post-hook and consumes stack cells fails this
check until it is either patched with revokes or explicitly audited.

Intended home: scripts/check-taint-hook-coverage.py (alongside the other
check-*.py lints); until then run manually from the worktree root.
"""

import re
import sys

PATH = 'category/vm/interpreter/instruction_table.hpp'

# Handlers audited as consuming zero stack cells (nothing to revoke).
ALLOWLIST = {'stop'}

def main():
    src = open(PATH).read()
    chunks = src.split('MONAD_VM_INSTRUCTION_CALL')
    failures = []
    for ch in chunks[1:]:
        m = re.match(r'\s*(?:inline\s+)?void\s+(\w+)\s*\(', ch)
        if not m:
            continue
        name = m.group(1)
        body = ch.split('MONAD_VM_INSTRUCTION_CALL')[0]
        if 'MONAD_VM_NEXT' in body:
            continue  # standard dispatch: post-hook applies
        if 'taint' in body:
            continue  # explicit handling
        if name in ALLOWLIST:
            continue
        failures.append(name)
    if failures:
        print('taint-hook coverage FAIL: custom-tail handlers without taint '
              'handling (patch them or add to the audited allowlist):')
        for name in failures:
            print('  ' + name)
        return 1
    print('taint-hook coverage OK')
    return 0

if __name__ == '__main__':
    sys.exit(main())
