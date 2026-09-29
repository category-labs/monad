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

//! secp256k1 public-key recovery: Q = u1·G + u2·R, with u1 = -z·r⁻¹ and
//! u2 = s·r⁻¹ (mod n), and R the curve point whose x is r.
//! G uses a static table of a·G + b·2^128·G, with six-bit a and b.
//! R uses a checked GLV split and signed four-bit windows over multiples of
//! R and φ(R). Both contributions share one doubling chain (Straus).
//! Verify all hints; handle equal/opposite points outside the curve-add precompile.

use ziskos::syscalls::SyscallPoint256;

use crate::ecrecover_tables::G_JOINT;

type Point = SyscallPoint256;

/// The group order n, little-endian limbs.
static N: [u64; 4] = [
    0xBFD25E8CD0364141,
    0xBAAEDCE6AF48A03B,
    0xFFFFFFFFFFFFFFFE,
    0xFFFFFFFFFFFFFFFF,
];
/// The field prime p.
static P: [u64; 4] = [
    0xFFFFFFFEFFFFFC2F,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
];
/// The cube root of unity in Fp that matches zisklib's λ: φ(P) = λ·P.
static BETA: [u64; 4] = [
    0xC1396C28719501EE,
    0x9CF0497512F58995,
    0x6E64479EAC3434E9,
    0x7AE96A2B657C0710,
];
/// zisklib's λ, the cube root of unity in Fn of its GLV split.
static LAMBDA: [u64; 4] = [
    0xDF02967C1B23BD72,
    0x122E22EA20816678,
    0xA5261C028812645A,
    0x5363AD4CC05C30E0,
];
static P_MINUS_ONE: [u64; 4] = [
    0xFFFFFFFEFFFFFC2E,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
    0xFFFFFFFFFFFFFFFF,
];
static ZERO: [u64; 4] = [0; 4];
static SEVEN: [u64; 4] = [7, 0, 0, 0];
/// A quadratic non-residue mod p: zisklib's NQR.
static NQR: [u64; 4] = [3, 0, 0, 0];

/// Matches SyscallArith256ModParams: d = (a·b + c) mod module.
#[repr(C)]
#[derive(Clone, Copy)]
struct MulModArgs {
    a: *const [u64; 4],
    b: *const [u64; 4],
    c: *const [u64; 4],
    module: *const [u64; 4],
    d: *mut [u64; 4],
}

/// Guest precompile calls; modular operations reuse their argument blocks.
#[cfg(all(target_os = "zkvm", target_vendor = "zisk"))]
mod op {
    use super::{MulModArgs, Point};

    // zisk_definitions::SYSCALL_ARITH256_MOD_ID, SYSCALL_SECP256K1_ADD_ID and
    // SYSCALL_SECP256K1_DBL_ID.
    const ARITH256_MOD: u16 = 0x802;
    const SECP256K1_ADD: u16 = 0x803;
    const SECP256K1_DBL: u16 = 0x804;

    #[inline(always)]
    pub unsafe fn add(p1: *mut Point, p2: *const Point) {
        core::arch::asm!(
            "csrs {port}, {p1}",
            "add x0, {p2}, x0",
            port = const SECP256K1_ADD,
            p1 = in(reg) p1,
            p2 = in(reg) p2,
            options(nostack),
        );
    }

    #[inline(always)]
    pub unsafe fn dbl(p: *mut Point) {
        core::arch::asm!("csrs {port}, {p}", port = const SECP256K1_DBL, p = in(reg) p);
    }

    #[inline(always)]
    pub unsafe fn mul_mod(args: *const MulModArgs) {
        core::arch::asm!("csrs {port}, {args}", port = const ARITH256_MOD, args = in(reg) args);
    }

    // Untrusted hints: send values via 0x8F0 or four-word pointers via 0x8F2;
    // invoke 0x8C0, then copy the answer via inputcpy (0x815). Verify before use.

    /// [is a square, the root of x of the given parity], or a root of 3·x.
    #[inline(always)]
    pub unsafe fn fcall_fp_sqrt(x: *const [u64; 4], parity: u64, result: *mut u64) {
        core::arch::asm!(
            "csrs 0x8F2, {x}",
            "csrs 0x8F0, {parity}",
            "csrwi 0x8C0, 3", // FCALL_SECP256K1_FP_SQRT_ID
            "csrs 0x815, {result}",
            "addi x0, {result}, 40",
            x = in(reg) x,
            parity = in(reg) parity,
            result = in(reg) result,
            options(nostack),
        );
    }

    /// x⁻¹ mod n.
    #[inline(always)]
    pub unsafe fn fcall_fn_inv(x: *const [u64; 4], result: *mut [u64; 4]) {
        core::arch::asm!(
            "csrs 0x8F2, {x}",
            "csrwi 0x8C0, 2", // FCALL_SECP256K1_FN_INV_ID
            "csrs 0x815, {result}",
            "addi x0, {result}, 32",
            x = in(reg) x,
            result = in(reg) result,
            options(nostack),
        );
    }

    /// [k1, k2, sigma1, sigma2] with (-1)^sigma1·k1 + (-1)^sigma2·k2·λ ≡ k (mod n).
    #[inline(always)]
    pub unsafe fn fcall_glv_decompose(k: *const [u64; 4], result: *mut [u64; 10]) {
        core::arch::asm!(
            "csrs 0x8F2, {k}",
            "csrwi 0x8C0, 4", // FCALL_SECP256K1_GLV_DECOMPOSE_ID
            "csrs 0x815, {result}",
            "addi x0, {result}, 80",
            k = in(reg) k,
            result = in(reg) result,
            options(nostack),
        );
    }

    /// Hide the pointer value from the optimizer to discourage repeated
    /// address reconstruction; the empty assembly emits no instruction.
    #[inline(always)]
    pub fn opaque<T>(mut p: *mut T) -> *mut T {
        unsafe {
            core::arch::asm!("/* {0} */", inout(reg) p, options(nomem, nostack, preserves_flags))
        };
        p
    }

    /// The constant, held in a register rather than rebuilt at each use.
    #[inline(always)]
    pub fn opaque_u64(mut v: u64) -> u64 {
        unsafe {
            core::arch::asm!("/* {0} */", inout(reg) v, options(nomem, nostack, preserves_flags))
        };
        v
    }
}

/// Everywhere else, ziskos's emulation of the same precompiles.
#[cfg(not(all(target_os = "zkvm", target_vendor = "zisk")))]
mod op {
    use super::{MulModArgs, Point};
    use ziskos::syscalls::{
        syscall_arith256_mod, syscall_secp256k1_add, syscall_secp256k1_dbl,
        SyscallArith256ModParams,
    };

    pub unsafe fn add(p1: *mut Point, p2: *const Point) {
        syscall_secp256k1_add(&mut *p1, &*p2);
    }

    pub unsafe fn dbl(p: *mut Point) {
        syscall_secp256k1_dbl(&mut *p);
    }

    pub unsafe fn mul_mod(args: *const MulModArgs) {
        let a = &*args;
        syscall_arith256_mod(&mut SyscallArith256ModParams {
            a: &*a.a,
            b: &*a.b,
            c: &*a.c,
            module: &*a.module,
            d: &mut *a.d,
        });
    }

    pub unsafe fn fcall_fp_sqrt(x: *const [u64; 4], parity: u64, result: *mut u64) {
        let r = ziskos::zisklib::fcall_secp256k1_fp_sqrt(&*x, parity);
        core::ptr::copy_nonoverlapping(r.as_ptr(), result, 5);
    }

    pub unsafe fn fcall_fn_inv(x: *const [u64; 4], result: *mut [u64; 4]) {
        *result = ziskos::zisklib::fcall_secp256k1_fn_inv(&*x);
    }

    pub unsafe fn fcall_glv_decompose(k: *const [u64; 4], result: *mut [u64; 10]) {
        *result = ziskos::zisklib::fcall_secp256k1_glv_decompose(&*k);
    }

    pub fn opaque<T>(p: *mut T) -> *mut T {
        core::hint::black_box(p)
    }

    pub fn opaque_u64(v: u64) -> u64 {
        core::hint::black_box(v)
    }
}

#[inline(always)]
fn limbs_less_than(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

#[inline(always)]
fn is_valid_scalar(x: &[u64; 4]) -> bool {
    x[0] | x[1] | x[2] | x[3] != 0 && limbs_less_than(x, &N)
}

/// -x mod n, for x < n.
#[inline(always)]
fn neg_mod_n(x: &[u64; 4]) -> [u64; 4] {
    if x[0] | x[1] | x[2] | x[3] == 0 {
        return *x;
    }
    let (d0, b0) = N[0].overflowing_sub(x[0]);
    let (d1, b1) = N[1].overflowing_sub(x[1]);
    let (d1, c1) = d1.overflowing_sub(b0 as u64);
    let (d2, b2) = N[2].overflowing_sub(x[2]);
    let (d2, c2) = d2.overflowing_sub((b1 | c1) as u64);
    let d3 = N[3].wrapping_sub(x[3]).wrapping_sub((b2 | c2) as u64);
    [d0, d1, d2, d3]
}

/// Rows 1..=8 of the R table are k·R, 9..=16 -k·R, 17..=24 φ(k·R),
/// 25..=32 -φ(k·R). Row 0 is unused; zero digits skip the addition.
const R_TABLE_ROWS: usize = 33;

/// Fixed working storage for sequential, non-reentrant recovery.
/// Preinitialized modular-operation arguments point into these fields.
#[repr(C)]
struct RecoveryState {
    r_squared: [u64; 4],
    /// r³ + 7
    curve_equation_value: [u64; 4],
    /// The root candidate's square.
    candidate_squared: [u64; 4],
    /// curve_equation_value·NQR
    nonresidue_product: [u64; 4],
    r_inverse: [u64; 4],
    /// r·r⁻¹
    inverse_check_product: [u64; 4],
    /// z·r⁻¹
    message_times_r_inverse: [u64; 4],
    /// s·r⁻¹
    u2: [u64; 4],
    signed_glv1: [u64; 4],
    signed_glv2: [u64; 4],
    /// λ·signed_glv2 + signed_glv1
    recomposed_glv_scalar: [u64; 4],
    glv_hint: [u64; 10],
    /// Row 1 is R itself: the square-root hint lands one word before its y, the
    /// flag in x[3], which r overwrites once the root is checked.
    table: [Point; R_TABLE_ROWS],
    accumulator: Point,
}

const ZERO_POINT: Point = Point {
    x: [0; 4],
    y: [0; 4],
};

static mut RECOVERY: RecoveryState = RecoveryState {
    r_squared: [0; 4],
    curve_equation_value: [0; 4],
    candidate_squared: [0; 4],
    nonresidue_product: [0; 4],
    r_inverse: [0; 4],
    inverse_check_product: [0; 4],
    message_times_r_inverse: [0; 4],
    u2: [0; 4],
    signed_glv1: [0; 4],
    signed_glv2: [0; 4],
    recomposed_glv_scalar: [0; 4],
    glv_hint: [0; 10],
    table: [ZERO_POINT; R_TABLE_ROWS],
    accumulator: ZERO_POINT,
};

/// Immutable pointer blocks; recovery writes their targets sequentially.
#[repr(transparent)]
struct Shared<T>(T);
unsafe impl<T> Sync for Shared<T> {}

/// Only caller-scalar pointers change per recovery; the other operands stay fixed.
#[repr(C)]
struct CallerScalarArgs {
    /// r·r
    r_squared: MulModArgs,
    /// r_squared·r + 7
    curve_equation_value: MulModArgs,
    /// z·r⁻¹
    message_times_r_inverse: MulModArgs,
    /// s·r⁻¹
    u2: MulModArgs,
}

// SAFETY (all the blocks below): only addresses of RECOVERY's fields are taken.
static mut CALLER_SCALAR_ARGS: CallerScalarArgs = unsafe {
    CallerScalarArgs {
        r_squared: MulModArgs {
            a: core::ptr::null(),
            b: core::ptr::null(),
            c: &ZERO,
            module: &P,
            d: &raw mut RECOVERY.r_squared,
        },
        curve_equation_value: MulModArgs {
            a: &raw const RECOVERY.r_squared,
            b: core::ptr::null(),
            c: &SEVEN,
            module: &P,
            d: &raw mut RECOVERY.curve_equation_value,
        },
        message_times_r_inverse: MulModArgs {
            a: core::ptr::null(),
            b: &raw const RECOVERY.r_inverse,
            c: &ZERO,
            module: &N,
            d: &raw mut RECOVERY.message_times_r_inverse,
        },
        u2: MulModArgs {
            a: core::ptr::null(),
            b: &raw const RECOVERY.r_inverse,
            c: &ZERO,
            module: &N,
            d: &raw mut RECOVERY.u2,
        },
    }
};

static CANDIDATE_SQUARED_ARGS: Shared<MulModArgs> = Shared(unsafe {
    MulModArgs {
        a: &raw const RECOVERY.table[1].y,
        b: &raw const RECOVERY.table[1].y,
        c: &ZERO,
        module: &P,
        d: &raw mut RECOVERY.candidate_squared,
    }
});
static NONRESIDUE_ARGS: Shared<MulModArgs> = Shared(unsafe {
    MulModArgs {
        a: &raw const RECOVERY.curve_equation_value,
        b: &NQR,
        c: &ZERO,
        module: &P,
        d: &raw mut RECOVERY.nonresidue_product,
    }
});
static INVERSE_CHECK_ARGS: Shared<MulModArgs> = Shared(unsafe {
    MulModArgs {
        a: &raw const RECOVERY.table[1].x,
        b: &raw const RECOVERY.r_inverse,
        c: &ZERO,
        module: &N,
        d: &raw mut RECOVERY.inverse_check_product,
    }
});
static GLV_RECOMPOSITION_ARGS: Shared<MulModArgs> = Shared(unsafe {
    MulModArgs {
        a: &LAMBDA,
        b: &raw const RECOVERY.signed_glv2,
        c: &raw const RECOVERY.signed_glv1,
        module: &N,
        d: &raw mut RECOVERY.recomposed_glv_scalar,
    }
});

/// For k = 1..8, compute φ(k·R).x = β·x and (-k·R).y = -y mod p.
static TABLE_ARGS: Shared<[MulModArgs; 16]> = Shared(unsafe {
    let unused = MulModArgs {
        a: core::ptr::null(),
        b: core::ptr::null(),
        c: core::ptr::null(),
        module: core::ptr::null(),
        d: core::ptr::null_mut(),
    };
    let mut args = [unused; 16];
    let mut k = 1;
    while k <= 8 {
        args[2 * k - 2] = MulModArgs {
            a: &BETA,
            b: &raw const RECOVERY.table[k].x,
            c: &ZERO,
            module: &P,
            d: &raw mut RECOVERY.table[16 + k].x,
        };
        args[2 * k - 1] = MulModArgs {
            a: &raw const RECOVERY.table[k].y,
            b: &P_MINUS_ONE,
            c: &ZERO,
            module: &P,
            d: &raw mut RECOVERY.table[8 + k].y,
        };
        k += 1;
    }
    args
});

/// Straus accumulator: at infinity, skip doubling and initialize by copying.
/// Precompiles cannot take infinity; all methods using this wrapper are inlined.
struct PointAccumulator {
    accumulator: *mut Point,
    at_infinity: bool,
}

impl PointAccumulator {
    #[inline(always)]
    unsafe fn double_twice(&mut self) {
        if !self.at_infinity {
            op::dbl(self.accumulator);
            op::dbl(self.accumulator);
        }
    }

    #[inline(always)]
    unsafe fn double_four_times(&mut self) {
        if !self.at_infinity {
            op::dbl(self.accumulator);
            op::dbl(self.accumulator);
            op::dbl(self.accumulator);
            op::dbl(self.accumulator);
        }
    }

    #[inline(always)]
    unsafe fn add(&mut self, addend: *const Point) {
        if self.at_infinity {
            initialize_accumulator(self.accumulator, addend);
            self.at_infinity = false;
        } else if (*self.accumulator).x[0] != (*addend).x[0] {
            op::add(self.accumulator, addend);
        } else {
            self.at_infinity = add_matching_x_low_limb(self.accumulator, addend);
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn initialize_accumulator(accumulator: *mut Point, addend: *const Point) {
    *accumulator = *addend;
}

/// Matching low x limbs may mean equal, opposite or distinct points.
/// Return true when their sum is the point at infinity.
#[cold]
#[inline(never)]
unsafe fn add_matching_x_low_limb(accumulator: *mut Point, addend: *const Point) -> bool {
    if (*accumulator).x != (*addend).x {
        op::add(accumulator, addend);
        false
    } else if (*accumulator).y == (*addend).y {
        op::dbl(accumulator);
        false
    } else {
        true
    }
}

/// For five-bit v, the signed Booth digit is ((v + 1) >> 1) - 16·(v >> 4).
/// Index by [GLV half][sign bit][v]: b1 selects ±R, b2 selects ±φ(R).
/// A null pointer marks digit zero; no point is added.
// SAFETY: only addresses of RECOVERY's rows are taken.
static BOOTH: Shared<[[[*const Point; 32]; 2]; 2]> = Shared(unsafe {
    let mut rows = [[[core::ptr::null::<Point>(); 32]; 2]; 2];
    let mut half_index = 0;
    while half_index < 2 {
        let mut sign_bit = 0;
        while sign_bit < 2 {
            let mut window_bits = 0;
            while window_bits < 32 {
                let digit = ((window_bits as i64 + 1) >> 1) - ((window_bits as i64 >> 4) << 4);
                if digit != 0 {
                    let negative = (digit < 0) as usize ^ sign_bit;
                    let row = 16 * half_index + negative * 8 + digit.unsigned_abs() as usize;
                    rows[half_index][sign_bit][window_bits] = &raw const RECOVERY.table[row];
                }
                window_bits += 1;
            }
            sign_bit += 1;
        }
        half_index += 1;
    }
    rows
});

/// From R in row 1: four doublings and three adds for 2R..8R, whose adds never
/// meet equal x: k·R = ±R would make R's order divide k ± 1, and n is prime.
#[inline(always)]
unsafe fn build_point_table(table_base: *mut Point) {
    let row = |k: usize| table_base.add(k);
    let add = |k: usize, j: usize| op::add(row(k), row(j));
    *row(2) = *row(1);
    op::dbl(row(2));
    *row(3) = *row(2);
    add(3, 1);
    *row(4) = *row(2);
    op::dbl(row(4));
    *row(5) = *row(4);
    add(5, 1);
    *row(6) = *row(3);
    op::dbl(row(6));
    *row(7) = *row(6);
    add(7, 1);
    *row(8) = *row(4);
    op::dbl(row(8));
    // β·x and -y = y·(positive - 1) mod positive straight into their rows.
    let args = op::opaque(TABLE_ARGS.0.as_ptr() as *mut MulModArgs);
    for k in 1..=8 {
        let (positive, neg, phi, neg_phi) = (row(k), row(8 + k), row(16 + k), row(24 + k));
        op::mul_mod(args.add(2 * k - 2));
        op::mul_mod(args.add(2 * k - 1));
        (*neg).x = (*positive).x;
        (*phi).y = (*positive).y;
        (*neg_phi).x = (*phi).x;
        (*neg_phi).y = (*neg).y;
    }
}

/// Read scalar bits 4J-1..=4J+3; bit -1 is zero for the first window.
#[inline(always)]
fn booth_bits<const J: u32>(scalar: &[u64; 4]) -> usize {
    let window_bits = if J == 0 {
        scalar[0] << 1
    } else if J < 16 {
        scalar[0] >> ((4 * J).wrapping_sub(1) & 63)
    } else if J == 16 {
        (scalar[0] >> 63) | (scalar[1] << 1)
    } else {
        scalar[1] >> ((4 * J).wrapping_sub(65) & 63)
    };
    (window_bits & 31) as usize
}

struct WindowOperands {
    r_windows: *const *const Point,
    phi_r_windows: *const *const Point,
    /// One row before `G_JOINT`: a·G + b·2^128·G is 64·(a + 64·b) bytes in.
    generator_bytes: *const u8,
    /// 63 << 6 and 63 << 12, the six bits of a and of b in that offset.
    low_offset_mask: u64,
    high_offset_mask: u64,
    b1: [u64; 4],
    b2: [u64; 4],
    u1: [u64; 4],
}

/// Extract six bits at 6*window_index into their byte-offset position.
/// The result is shifted left by `shift`; `mask` is 63 << shift.
#[inline(always)]
fn six_bits_shifted(lo: u64, hi: u64, window_index: u32, shift: u32, mask: u64) -> u64 {
    let bit_offset = 6 * window_index;
    if bit_offset + 6 <= 64 {
        if bit_offset >= shift {
            (lo >> ((bit_offset - shift) & 63)) & mask
        } else {
            (lo << ((shift - bit_offset) & 63)) & mask
        }
    } else if bit_offset < 64 {
        (((lo >> (bit_offset & 63)) | (hi << ((64 - bit_offset) & 63))) & 63) << shift
    } else if bit_offset - 64 >= shift {
        (hi >> ((bit_offset - 64 - shift) & 63)) & mask
    } else {
        (hi << ((shift - (bit_offset - 64)) & 63)) & mask
    }
}

/// Add the G contribution of the window at bit 6*window_index.
#[inline(always)]
unsafe fn add_generator_window(
    chain: &mut PointAccumulator,
    operands: &WindowOperands,
    window_index: u32,
) {
    let byte_offset = six_bits_shifted(
        operands.u1[0],
        operands.u1[1],
        window_index,
        6,
        operands.low_offset_mask,
    ) | six_bits_shifted(
        operands.u1[2],
        operands.u1[3],
        window_index,
        12,
        operands.high_offset_mask,
    );
    // Zero only when twelve bits of u1 are.
    if byte_offset != 0 {
        // generator_bytes lies one row before G_JOINT, outside the table, so
        // only wrapping_add may offset it.
        chain.add(operands.generator_bytes.wrapping_add(byte_offset as usize) as *const Point);
    }
}

/// Window j: four doublings, then the digits of weight 16^j. A G window m
/// weighs 2^(6m): 16^j itself when m is even, 4·16^j when m is odd, which is
/// halfway through the window's doublings.
#[inline(always)]
unsafe fn apply_window<const J: u32>(chain: &mut PointAccumulator, operands: &WindowOperands) {
    if J != 32 {
        if (4 * J + 2) % 6 == 0 {
            chain.double_twice();
            add_generator_window(chain, operands, (4 * J + 2) / 6);
            chain.double_twice();
        } else {
            chain.double_four_times();
        }
    }
    let row = *operands.r_windows.add(booth_bits::<J>(&operands.b1));
    if !row.is_null() {
        chain.add(row);
    }
    let row = *operands.phi_r_windows.add(booth_bits::<J>(&operands.b2));
    if !row.is_null() {
        chain.add(row);
    }
    if (4 * J) % 6 == 0 && J < 32 {
        add_generator_window(chain, operands, 4 * J / 6);
    }
}

/// u1·G + u2·R into the accumulator, false at infinity, for R in row 1 and
/// u2 = (-1)^sigma1·b1 + (-1)^sigma2·b2·λ.
fn double_scalar_mul(u1: &[u64; 4], b1: [u64; 4], b2: [u64; 4], sigma1: u64, sigma2: u64) -> bool {
    // SAFETY: rows 2..=32 are written before the windows read them. The first
    // add initializes the accumulator while `at_infinity` is true.
    unsafe {
        let point_table = op::opaque((&raw mut RECOVERY.table).cast::<Point>());
        build_point_table(point_table);
        let accumulator = op::opaque(&raw mut RECOVERY.accumulator);
        let mut chain = PointAccumulator {
            accumulator,
            at_infinity: true,
        };
        let operands = WindowOperands {
            r_windows: op::opaque(BOOTH.0[0][sigma1 as usize].as_ptr() as *mut *const Point),
            phi_r_windows: op::opaque(BOOTH.0[1][sigma2 as usize].as_ptr() as *mut *const Point),
            generator_bytes: op::opaque(
                (G_JOINT.as_ptr() as *const u8).wrapping_sub(core::mem::size_of::<Point>())
                    as *mut u8,
            ),
            low_offset_mask: op::opaque_u64(63 << 6),
            high_offset_mask: op::opaque_u64(63 << 12),
            b1,
            b2,
            u1: *u1,
        };
        macro_rules! windows {
            ($($j:literal)*) => { $(apply_window::<$j>(&mut chain, &operands);)* };
        }
        windows!(32 31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0);
        !chain.at_infinity
    }
}

/// Recover the key for hash z, signature (r, s) and recovery id `recid`.
/// Scalars use little-endian limbs; `pubkey` receives big-endian x || y.
/// Return false without writing for r/s outside [1, n), recid > 1,
/// no curve point with x = r, or a recovered key at infinity.
///
/// # Safety
/// `z`, `r` and `s` point to four readable limbs each; `pubkey` to eight
/// writable words. All pointers are 8-aligned. RECOVERY is not reentrant.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_recover(
    z: *const [u64; 4],
    r: *const [u64; 4],
    s: *const [u64; 4],
    recid: u8,
    pubkey: *mut [u64; 8],
) -> bool {
    if recid > 1 || !is_valid_scalar(&*r) || !is_valid_scalar(&*s) {
        return false;
    }
    let state = op::opaque(&raw mut RECOVERY);
    let scalar_args = op::opaque(&raw mut CALLER_SCALAR_ARGS);
    // R = (r, y) must satisfy y² = r³ + 7, with y of parity recid.
    (*scalar_args).r_squared.a = r;
    (*scalar_args).r_squared.b = r;
    op::mul_mod(&raw const (*scalar_args).r_squared);
    (*scalar_args).curve_equation_value.b = r;
    op::mul_mod(&raw const (*scalar_args).curve_equation_value);
    // The untrusted hint gives a root of r³ + 7, or of NQR·(r³ + 7)
    // to justify rejection. Verify the corresponding square before use.
    op::fcall_fp_sqrt(
        &raw const (*state).curve_equation_value,
        recid as u64,
        (&raw mut (*state).table[1].x).cast::<u64>().add(3),
    );
    let claims_square_root = (*state).table[1].x[3] == 1;
    let root_candidate = &raw const (*state).table[1].y;
    assert!(
        limbs_less_than(&*root_candidate, &P),
        "Square root is not canonical"
    );
    op::mul_mod(&CANDIDATE_SQUARED_ARGS.0);
    if !claims_square_root {
        // Verify the non-residue claim before rejecting the signature.
        op::mul_mod(&NONRESIDUE_ARGS.0);
        assert!(
            (*state).candidate_squared == (*state).nonresidue_product,
            "Square root verification failed"
        );
        return false;
    }
    assert!(
        (*state).candidate_squared == (*state).curve_equation_value,
        "Square root verification failed"
    );
    assert!(
        (*root_candidate)[0] & 1 == recid as u64,
        "Parity of the square root does not match"
    );
    (*state).table[1].x = *r;
    // r⁻¹ mod n.
    op::fcall_fn_inv(&raw const (*state).table[1].x, &raw mut (*state).r_inverse);
    assert!(
        limbs_less_than(&(*state).r_inverse, &N),
        "Inverse is not canonical"
    );
    op::mul_mod(&INVERSE_CHECK_ARGS.0);
    assert!(
        (*state).inverse_check_product == [1, 0, 0, 0],
        "Inverse check failed"
    );
    // u1 = -z·r⁻¹, u2 = s·r⁻¹ mod n.
    (*scalar_args).message_times_r_inverse.a = z;
    op::mul_mod(&raw const (*scalar_args).message_times_r_inverse);
    let u1 = neg_mod_n(&(*state).message_times_r_inverse);
    (*scalar_args).u2.a = s;
    op::mul_mod(&raw const (*scalar_args).u2);
    // u2 = (-1)^sigma1·b1 + (-1)^sigma2·b2·λ mod n, b1, b2 < 2^128.
    op::fcall_glv_decompose(&raw const (*state).u2, &raw mut (*state).glv_hint);
    let glv_hint = &(*state).glv_hint;
    assert!(
        glv_hint[2] | glv_hint[3] | glv_hint[6] | glv_hint[7] == 0,
        "GLV: a half-scalar exceeds 2^128"
    );
    assert!(
        glv_hint[8] <= 1 && glv_hint[9] <= 1,
        "GLV: a sign is not a bit"
    );
    let (b1, b2) = (
        [glv_hint[0], glv_hint[1], 0, 0],
        [glv_hint[4], glv_hint[5], 0, 0],
    );
    let (sigma1, sigma2) = (glv_hint[8], glv_hint[9]);
    // Signed GLV components represented as residues modulo n.
    (*state).signed_glv1 = if sigma1 == 1 { neg_mod_n(&b1) } else { b1 };
    (*state).signed_glv2 = if sigma2 == 1 { neg_mod_n(&b2) } else { b2 };
    op::mul_mod(&GLV_RECOMPOSITION_ARGS.0);
    assert!(
        (*state).recomposed_glv_scalar == (*state).u2,
        "GLV decomposition relation failed"
    );
    if !double_scalar_mul(&u1, b1, b2, sigma1, sigma2) {
        return false;
    }
    // The caller's output buffer is uninitialized; write through raw pointers.
    let public_key = &raw const (*state).accumulator;
    let output_words = pubkey.cast::<u64>();
    for i in 0..4 {
        output_words.add(i).write((*public_key).x[3 - i].to_be());
        output_words
            .add(4 + i)
            .write((*public_key).y[3 - i].to_be());
    }
    true
}
