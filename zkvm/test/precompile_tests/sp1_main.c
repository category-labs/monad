// Copyright (C) 2025-26 Category Labs, Inc.
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
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// SP1 full-SDK entry for the precompile golden-vector test guest. Mirrors the
// witness entry (zkvm/sp1/program/main.c) but hands control to the
// precompile-test C++ entry, which reads a serialized vector blob via
// read_input and commits a PR01 summary via write_output.

extern void monad_zkvm_run_precompile_tests(void);

// C++ static constructors, bounded by the symbols zkvm.ld places around the
// .init_array section. SP1's `_start` (built for Rust guests) does not run
// them, so we must before touching any guest global.
extern void (*__init_array_start[])(void);
extern void (*__init_array_end[])(void);

static void run_init_array(void)
{
    for (void (**fn)(void) = __init_array_start; fn != __init_array_end; ++fn) {
        (*fn)();
    }
}

int main(void)
{
    run_init_array();
    monad_zkvm_run_precompile_tests();
    return 0;
}
