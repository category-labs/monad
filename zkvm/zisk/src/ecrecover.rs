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
//!
//! zisklib's `glv_double_scalar_mul_with_g_secp256k1` walks the four GLV
//! half-scalars a bit at a time: every bit tests four scalars and dispatches
//! on the sixteen cases, about 35 steps a bit against a 1,440-cell doubling.
//! Here the bits go four at a time, and the adds are fewer:
//!
//! - u1 against G, six bits of both halves at once: u1 = lo + 2^128·hi, and
//!   the bits 6m..6m+5 of lo and of hi, a and b, are one add of the static
//!   a·G + b·2^128·G (`G_JOINT`). No decomposition, 22 adds.
//! - u2 against R through GLV, u2 = ±b1 ± b2·λ with b1, b2 < 2^128, each
//!   written in signed radix 16 (Booth: digits -8..=8, read straight off five
//!   bits, no carry to propagate) against 1·R..8·R and their images under
//!   φ(x, y) = (β·x, y) = λ·(x, y), both signs of each. About 59 adds.
//!
//! The two meet in one chain of 128 doublings (Straus): radix-16 window j is
//! four doublings, then the digits of weight 16^j.
//!
//! The hints are checked as zisklib checks them, and one that fails aborts:
//! the square root that lifts R canonical and squared back (a claimed
//! non-residue through the root of its product with the non-residue 3), r⁻¹
//! canonical and multiplied back, the GLV split bounded and recombined. The
//! curve precompile needs two points of different x: an add whose x equals
//! the accumulator's is resolved here instead -- a doubling when the points
//! are equal, the point at infinity when they are opposite.

use core::mem::MaybeUninit;

use ziskos::syscalls::SyscallPoint256;
use ziskos::zisklib::{
    fcall_secp256k1_fn_inv, fcall_secp256k1_fp_sqrt, fcall_secp256k1_glv_decompose,
};

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

/// The argument block of the curve add, as ziskos's SyscallSecp256k1AddParams:
/// p1 += p2.
#[repr(C)]
struct AddArgs {
    p1: *mut Point,
    p2: *const Point,
}

/// The argument block of the modular multiply-add, as ziskos's
/// SyscallArith256ModParams: d = a·b + c mod module.
#[repr(C)]
struct MulModArgs {
    a: *const [u64; 4],
    b: *const [u64; 4],
    c: *const [u64; 4],
    module: *const [u64; 4],
    d: *mut [u64; 4],
}

/// The precompiles, issued here rather than through ziskos's wrappers, which
/// take references: a block built afresh for every add is two stores and the
/// address of each operand rebuilt, where the accumulator's block is built
/// once and an add stores only its second point.
#[cfg(all(target_os = "zkvm", target_vendor = "zisk"))]
mod op {
    use super::{AddArgs, MulModArgs, Point};

    // zisk_definitions::SYSCALL_ARITH256_MOD_ID, SYSCALL_SECP256K1_ADD_ID and
    // SYSCALL_SECP256K1_DBL_ID.
    const ARITH256_MOD: u16 = 0x802;
    const SECP256K1_ADD: u16 = 0x803;
    const SECP256K1_DBL: u16 = 0x804;

    #[inline(always)]
    pub unsafe fn add(args: *mut AddArgs) {
        core::arch::asm!("csrs {port}, {args}", port = const SECP256K1_ADD, args = in(reg) args);
    }

    #[inline(always)]
    pub unsafe fn dbl(p: *mut Point) {
        core::arch::asm!("csrs {port}, {p}", port = const SECP256K1_DBL, p = in(reg) p);
    }

    #[inline(always)]
    pub unsafe fn mul_mod(args: *mut MulModArgs) {
        core::arch::asm!("csrs {port}, {args}", port = const ARITH256_MOD, args = in(reg) args);
    }

    /// The pointer, as a value the compiler cannot rebuild from the stack
    /// pointer at each use: two instructions for a frame this size.
    #[inline(always)]
    pub fn opaque<T>(mut p: *mut T) -> *mut T {
        unsafe {
            core::arch::asm!("/* {0} */", inout(reg) p, options(nomem, nostack, preserves_flags))
        };
        p
    }
}

/// Everywhere else, ziskos's emulation of the same precompiles.
#[cfg(not(all(target_os = "zkvm", target_vendor = "zisk")))]
mod op {
    use super::{AddArgs, MulModArgs, Point};
    use ziskos::syscalls::{
        syscall_arith256_mod, syscall_secp256k1_add, syscall_secp256k1_dbl,
        SyscallArith256ModParams, SyscallSecp256k1AddParams,
    };

    pub unsafe fn add(args: *mut AddArgs) {
        let a = &*args;
        syscall_secp256k1_add(&mut SyscallSecp256k1AddParams {
            p1: &mut *a.p1,
            p2: &*a.p2,
        });
    }

    pub unsafe fn dbl(p: *mut Point) {
        syscall_secp256k1_dbl(&mut *p);
    }

    pub unsafe fn mul_mod(args: *mut MulModArgs) {
        let a = &*args;
        syscall_arith256_mod(&mut SyscallArith256ModParams {
            a: &*a.a,
            b: &*a.b,
            c: &*a.c,
            module: &*a.module,
            d: &mut *a.d,
        });
    }

    pub fn opaque<T>(p: *mut T) -> *mut T {
        core::hint::black_box(p)
    }
}

/// a < b.
#[inline(always)]
fn lt(a: &[u64; 4], b: &[u64; 4]) -> bool {
    for i in (0..4).rev() {
        if a[i] != b[i] {
            return a[i] < b[i];
        }
    }
    false
}

/// 0 < x < n.
#[inline(always)]
fn is_scalar(x: &[u64; 4]) -> bool {
    x[0] | x[1] | x[2] | x[3] != 0 && lt(x, &N)
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

/// a·b + c mod m, through the one argument block `args`.
#[inline(always)]
unsafe fn mul_mod(
    args: *mut MulModArgs,
    a: &[u64; 4],
    b: &[u64; 4],
    c: &[u64; 4],
    m: &[u64; 4],
) -> [u64; 4] {
    let mut d = MaybeUninit::<[u64; 4]>::uninit();
    *args = MulModArgs {
        a,
        b,
        c,
        module: m,
        d: d.as_mut_ptr(),
    };
    op::mul_mod(args);
    d.assume_init()
}

/// The Straus accumulator. It starts at the point at infinity, which the
/// precompiles cannot take: while `inf` holds, a doubling is skipped and an
/// add is a copy. `args.p1` is `acc` throughout. Never passed to a call that
/// is not inlined, so its three fields live in registers.
struct Chain {
    acc: *mut Point,
    args: *mut AddArgs,
    inf: bool,
}

impl Chain {
    #[inline(always)]
    unsafe fn dbl2(&mut self) {
        if !self.inf {
            op::dbl(self.acc);
            op::dbl(self.acc);
        }
    }

    #[inline(always)]
    unsafe fn dbl4(&mut self) {
        if !self.inf {
            op::dbl(self.acc);
            op::dbl(self.acc);
            op::dbl(self.acc);
            op::dbl(self.acc);
        }
    }

    #[inline(always)]
    unsafe fn add(&mut self, t: *const Point) {
        if self.inf {
            restart(self.acc, t);
            self.inf = false;
        } else if (*self.acc).x[0] != (*t).x[0] {
            (*self.args).p2 = t;
            op::add(self.args);
        } else {
            self.inf = add_same_x0(self.acc, self.args, t);
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn restart(acc: *mut Point, t: *const Point) {
    *acc = *t;
}

/// The low limbs of x agree: equal points, opposite points, or -- the only
/// case an honest block reaches -- neither. True when the sum is the point at
/// infinity.
#[cold]
#[inline(never)]
unsafe fn add_same_x0(acc: *mut Point, args: *mut AddArgs, t: *const Point) -> bool {
    if (*acc).x != (*t).x {
        (*args).p2 = t;
        op::add(args);
        false
    } else if (*acc).y == (*t).y {
        op::dbl(acc);
        false
    } else {
        true
    }
}

/// Byte offsets into the R table (`RTable`) of the point for each Booth
/// window value: the digit d of the five bits v is ((v + 1) >> 1) - 16·(v >> 4),
/// its point d·(±R) or d·(±φ(R)), and 0 marks d = 0. `sigma` is the sign GLV
/// puts on the half-scalar.
const fn booth_offsets(base: u64, sigma: u64) -> [u64; 32] {
    let mut o = [0u64; 32];
    let mut v = 0;
    while v < 32 {
        let d = ((v as i64 + 1) >> 1) - ((v as i64 >> 4) << 4);
        if d != 0 {
            let neg = (d < 0) as u64 ^ sigma;
            o[v] = (base + neg * 8 + d.unsigned_abs()) * core::mem::size_of::<Point>() as u64;
        }
        v += 1;
    }
    o
}

/// `[half-scalar][sigma]`: b1 reads the R rows, b2 the φ(R) rows.
static BOOTH: [[[u64; 32]; 2]; 2] = [
    [booth_offsets(0, 0), booth_offsets(0, 1)],
    [booth_offsets(16, 0), booth_offsets(16, 1)],
];

/// Row 0 is never read (offset 0 is the zero digit); rows 1..=8 are k·R,
/// 9..=16 -k·R, 17..=24 φ(k·R), 25..=32 -φ(k·R).
type RTable = [Point; 33];

/// Four doublings and three adds for 2R..8R, whose adds never meet equal x:
/// k·R = ±R would make R's order divide k ± 1, and n is prime.
#[inline(always)]
unsafe fn build_table(t: *mut Point, r: &Point, args: *mut AddArgs) {
    let row = |k: usize| t.add(k);
    let add = |k: usize, j: usize| {
        (*args).p1 = row(k);
        (*args).p2 = row(j);
        op::add(args);
    };
    *row(1) = *r;
    *row(2) = *r;
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
    // β·x and -y = y·(p - 1) mod p straight into their rows: one argument
    // block, of which only the operands and the destination change.
    let mut mm = MulModArgs {
        a: core::ptr::null(),
        b: core::ptr::null(),
        c: &ZERO,
        module: &P,
        d: core::ptr::null_mut(),
    };
    let mm = op::opaque(&mut mm as *mut MulModArgs);
    for k in 1..=8 {
        let (p, neg, phi, neg_phi) = (row(k), row(8 + k), row(16 + k), row(24 + k));
        (*mm).a = &BETA;
        (*mm).b = &(*p).x;
        (*mm).d = &mut (*phi).x;
        op::mul_mod(mm);
        (*mm).a = &(*p).y;
        (*mm).b = &P_MINUS_ONE;
        (*mm).d = &mut (*neg).y;
        op::mul_mod(mm);
        (*neg).x = (*p).x;
        (*phi).y = (*p).y;
        (*neg_phi).x = (*phi).x;
        (*neg_phi).y = (*neg).y;
    }
}

/// The five bits 4j-1..=4j+3 of a 128-bit b, bit -1 being 0.
#[inline(always)]
fn booth_bits<const J: u32>(b: &[u64; 4]) -> usize {
    let v = if J == 0 {
        b[0] << 1
    } else if J < 16 {
        b[0] >> ((4 * J).wrapping_sub(1) & 63)
    } else if J == 16 {
        (b[0] >> 63) | (b[1] << 1)
    } else {
        b[1] >> ((4 * J).wrapping_sub(65) & 63)
    };
    (v & 31) as usize
}

/// The operands of the windows, each held in a register.
struct Operands {
    t: *const u8,
    booth1: *const u64,
    booth2: *const u64,
    /// One row before `G_JOINT`: indexed by a + 64·b itself.
    g: *const Point,
    b1: [u64; 4],
    b2: [u64; 4],
    u1: [u64; 4],
}

/// Bits 6m..6m+5 of a 128-bit value.
#[inline(always)]
fn six_bits(lo: u64, hi: u64, m: u32) -> u64 {
    let s = 6 * m;
    let v = if s + 6 <= 64 {
        lo >> (s & 63)
    } else if s < 64 {
        (lo >> (s & 63)) | (hi << ((64 - s) & 63))
    } else {
        hi >> ((s - 64) & 63)
    };
    v & 63
}

/// The G digit of weight 2^(6m).
#[inline(always)]
unsafe fn g_window(c: &mut Chain, o: &Operands, m: u32) {
    let idx = six_bits(o.u1[0], o.u1[1], m) | six_bits(o.u1[2], o.u1[3], m) << 6;
    if idx != 0 {
        c.add(o.g.add(idx as usize));
    }
}

/// Window j: four doublings, then the digits of weight 16^j. A G window m
/// weighs 2^(6m): 16^j itself when m is even, 4·16^j when m is odd, which is
/// halfway through the window's doublings.
#[inline(always)]
unsafe fn window<const J: u32>(c: &mut Chain, o: &Operands) {
    if J != 32 {
        if (4 * J + 2) % 6 == 0 {
            c.dbl2();
            g_window(c, o, (4 * J + 2) / 6);
            c.dbl2();
        } else {
            c.dbl4();
        }
    }
    let off = *o.booth1.add(booth_bits::<J>(&o.b1));
    if off != 0 {
        c.add(o.t.add(off as usize) as *const Point);
    }
    let off = *o.booth2.add(booth_bits::<J>(&o.b2));
    if off != 0 {
        c.add(o.t.add(off as usize) as *const Point);
    }
    if (4 * J) % 6 == 0 && J < 32 {
        g_window(c, o, 4 * J / 6);
    }
}

/// u1·G + u2·R, None at infinity, for u2 = (-1)^sigma1·b1 + (-1)^sigma2·b2·λ.
fn double_scalar_mul(
    u1: &[u64; 4],
    b1: [u64; 4],
    b2: [u64; 4],
    sigma1: u64,
    sigma2: u64,
    r: &Point,
) -> Option<Point> {
    let mut table = MaybeUninit::<RTable>::uninit();
    let mut acc = MaybeUninit::<Point>::uninit();
    let mut args = AddArgs {
        p1: core::ptr::null_mut(),
        p2: core::ptr::null(),
    };
    // SAFETY: the table's rows 1..=32 are written before the windows read
    // them, and `acc` is written by the first add, which `inf` makes a copy.
    unsafe {
        let t = op::opaque(table.as_mut_ptr() as *mut Point);
        let args = op::opaque(&mut args as *mut AddArgs);
        build_table(t, r, args);
        let acc = op::opaque(acc.as_mut_ptr());
        (*args).p1 = acc;
        let mut c = Chain {
            acc,
            args,
            inf: true,
        };
        let o = Operands {
            t: t as *const u8,
            booth1: op::opaque(BOOTH[0][sigma1 as usize].as_ptr() as *mut u64),
            booth2: op::opaque(BOOTH[1][sigma2 as usize].as_ptr() as *mut u64),
            g: op::opaque(G_JOINT.as_ptr().wrapping_sub(1) as *mut Point),
            b1,
            b2,
            u1: *u1,
        };
        macro_rules! windows {
            ($($j:literal)*) => { $(window::<$j>(&mut c, &o);)* };
        }
        windows!(32 31 30 29 28 27 26 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0);
        if c.inf {
            None
        } else {
            Some(*acc)
        }
    }
}

/// Recovers the public key that signed the 32-byte hash z with (r, s) and
/// recovery id `recid`, all scalars as little-endian 64-bit limbs, and writes
/// it as x || y, each big-endian, into `pubkey`. False, with `pubkey`
/// untouched, when r or s is outside [1, n), `recid` exceeds 1, no curve point
/// has x = r, or the key would be the point at infinity.
///
/// # Safety
/// `z`, `r` and `s` point to four readable limbs each; `pubkey` to eight
/// writable, 8-aligned words.
#[no_mangle]
pub unsafe extern "C" fn monad_zkvm_secp256k1_recover(
    z: *const [u64; 4],
    r: *const [u64; 4],
    s: *const [u64; 4],
    recid: u8,
    pubkey: *mut [u64; 8],
) -> bool {
    let (z, r, s) = (&*z, &*r, &*s);
    if recid > 1 || !is_scalar(r) || !is_scalar(s) {
        return false;
    }
    let mut args = MaybeUninit::<MulModArgs>::uninit();
    let args = op::opaque(args.as_mut_ptr());
    // R = (r, y) with y² = r³ + 7, y of parity recid.
    let x2 = mul_mod(args, r, r, &ZERO, &P);
    let y2 = mul_mod(args, &x2, r, &SEVEN, &P);
    let h = fcall_secp256k1_fp_sqrt(&y2, recid as u64);
    let y = [h[1], h[2], h[3], h[4]];
    assert!(lt(&y, &P), "Square root is not canonical");
    let yy = mul_mod(args, &y, &y, &ZERO, &P);
    if h[0] != 1 {
        let t = mul_mod(args, &y2, &NQR, &ZERO, &P);
        assert!(yy == t, "Square root verification failed");
        return false;
    }
    assert!(yy == y2, "Square root verification failed");
    assert!(
        y[0] & 1 == recid as u64,
        "Parity of the square root does not match"
    );
    // r⁻¹ mod n.
    let r_inv = fcall_secp256k1_fn_inv(r);
    assert!(lt(&r_inv, &N), "Inverse is not canonical");
    let one = mul_mod(args, r, &r_inv, &ZERO, &N);
    assert!(one == [1, 0, 0, 0], "Inverse check failed");
    // u1 = -z·r⁻¹, u2 = s·r⁻¹ mod n.
    let u1 = neg_mod_n(&mul_mod(args, z, &r_inv, &ZERO, &N));
    let u2 = mul_mod(args, s, &r_inv, &ZERO, &N);
    // u2 = (-1)^sigma1·b1 + (-1)^sigma2·b2·λ mod n, b1, b2 < 2^128.
    let h = fcall_secp256k1_glv_decompose(&u2);
    assert!(
        h[2] | h[3] | h[6] | h[7] == 0,
        "GLV: a half-scalar exceeds 2^128"
    );
    assert!(h[8] <= 1 && h[9] <= 1, "GLV: a sign is not a bit");
    let (b1, b2) = ([h[0], h[1], 0, 0], [h[4], h[5], 0, 0]);
    let k1 = if h[8] == 1 { neg_mod_n(&b1) } else { b1 };
    let k2 = if h[9] == 1 { neg_mod_n(&b2) } else { b2 };
    assert!(
        mul_mod(args, &LAMBDA, &k2, &k1, &N) == u2,
        "GLV decomposition relation failed"
    );
    let rp = Point { x: *r, y };
    let Some(q) = double_scalar_mul(&u1, b1, b2, h[8], h[9], &rp) else {
        return false;
    };
    let out = &mut *pubkey;
    for i in 0..4 {
        out[i] = q.x[3 - i].to_be();
        out[4 + i] = q.y[3 - i].to_be();
    }
    true
}
