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

// SP1 full-SDK guest entry.
//
// We link against the vendored SP1 zkEVM SDK (zkvm/sp1/sdk/libzkevm.a), which
// supplies `_start` (the SP1 runtime entry, which calls `main`), the
// allocator, the eth-act IO ABI (`read_input` / `write_output`), `zkvm_halt`,
// and every `zkvm_*` accelerator. So all this program does is hand control to
// the C++ guest's `monad_zkvm_execute_witness`, which reads the witness via
// `read_input` and emits the post-state root via `write_output`.
//
// Kept as a standalone object (not folded into the guest archive) so the
// linker always pulls `main` in to satisfy `_start`'s reference to it.

extern void monad_zkvm_execute_witness(void);

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
    monad_zkvm_execute_witness();
    return 0;
}
