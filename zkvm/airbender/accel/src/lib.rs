// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

//! The zkvm_* accelerators of zkvm_accelerators.h on Airbender, over
//! airbender-crypto with its "proving" features (bigint and keccak
//! delegations), the same code ZKsync OS proves blocks with.

#![no_std]

extern crate alloc;

use airbender_crypto::ripemd160::{Digest as _, Ripemd160};
use airbender_crypto::secp256k1::recover_from_bytes_with_hooks;
use airbender_crypto::sha256::Sha256;
use core::alloc::{GlobalAlloc, Layout};

extern "C" {
    fn sys_alloc_aligned(size: usize, align: usize) -> *mut u8;
    fn abort() -> !;
    fn monad_zkvm_airbender_print(s: *const u8, len: usize);
}

const ZKVM_EOK: i32 = 0;
const ZKVM_EFAIL: i32 = -1;

/// The guest's bump arena (runtime.c); frees are dropped, as the C++ side's are.
struct Arena;

unsafe impl GlobalAlloc for Arena {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        sys_alloc_aligned(layout.size(), layout.align())
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ARENA: Arena = Arena;

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    const MSG: &[u8] = b"panic in the Airbender accelerators";
    unsafe {
        monad_zkvm_airbender_print(MSG.as_ptr(), MSG.len());
        abort()
    }
}

/// secp256k1 field hints from the host (zkvm/airbender/runner), each checked
/// with one multiplication, as ZKsync OS's `Secp256k1HooksWithOracle` takes
/// them from its oracle (basic_system field_ops.rs). With division cheap,
/// recovery runs in affine coordinates (airbender-crypto recover_affine.rs):
/// a group operation is a hinted slope and two or three multiplications,
/// where the Jacobian formulas take 7 to 11.
mod hints {
    use airbender_crypto::secp256k1::{
        field::FieldElement, hooks::Secp256k1Hooks, scalars::Scalar,
    };
    use airbender_crypto::{bigint_op_delegation_raw, BigIntOps};
    use core::mem::MaybeUninit;

    // A query is its tag, then the operand's address, through the
    // non-determinism CSR (the division queries' protocol, uint256.hpp); the
    // host reads the operand there and answers in the same representation:
    // Montgomery words, least significant first.
    /// The numerator and the denominator, adjacent: their quotient.
    const DIVIDE: u32 = 0x4d44_5610;
    /// x: x^((p+1)/4), then a word, non-zero if x is not a square.
    const SQRT: u32 = 0x4d44_5611;
    /// x: 1/x.
    const INVERT: u32 = 0x4d44_5612;
    /// s: 1/s modulo the group order.
    const SCALAR_INVERT: u32 = 0x4d44_5613;

    /// `2^256 mod p` and `2^256 mod n`: the words of one.
    const R_MOD_P: [u32; 8] = [0x3d1, 0x1, 0, 0, 0, 0, 0, 0];
    const R_MOD_N: [u32; 8] = [
        0x2fc9bebf, 0x402da173, 0x50b75fc4, 0x45512319, 0x1, 0, 0, 0,
    ];

    const fn words_of<T>(value: &T) -> [u32; 8] {
        // SAFETY: T is 32 bytes (checked below); const evaluation refuses
        // padding
        unsafe { core::ptr::read(core::ptr::from_ref(value).cast::<[u32; 8]>()) }
    }

    const fn words_eq(a: &[u32; 8], b: &[u32; 8]) -> bool {
        let mut i = 0;
        while i < 8 {
            if a[i] != b[i] {
                return false;
            }
            i += 1;
        }
        true
    }

    // The host reads and answers Montgomery words: a change of airbender-
    // crypto's representation must stop the build here.
    const _: () = {
        assert!(core::mem::size_of::<FieldElement>() == 32);
        assert!(core::mem::align_of::<FieldElement>() >= 32);
        assert!(core::mem::size_of::<Scalar>() == 32);
        assert!(core::mem::align_of::<Scalar>() >= 32);
        assert!(words_eq(&words_of(&FieldElement::ONE), &R_MOD_P));
        assert!(words_eq(&words_of(&FieldElement::ZERO), &[0; 8]));
        assert!(words_eq(&words_of(&Scalar::ONE), &R_MOD_N));
        assert!(words_eq(&words_of(&Scalar::ZERO), &[0; 8]));
    };

    /// A delegation operand: 32-byte aligned, and in RAM as .rodata is.
    #[repr(C, align(32))]
    struct Operand([u32; 8]);

    static P: Operand = Operand([
        0xfffffc2f, 0xfffffffe, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff, 0xffffffff,
        0xffffffff,
    ]);
    static N: Operand = Operand([
        0xd0364141, 0xbfd25e8c, 0xaf48a03b, 0xbaaedce6, 0xfffffffe, 0xffffffff, 0xffffffff,
        0xffffffff,
    ]);

    #[inline(always)]
    fn write(w: u32) {
        // asm! may touch memory: the operand is stored before the host reads it
        unsafe { core::arch::asm!("csrrw x0, 0x7c0, {0}", in(reg) w, options(nostack)) }
    }

    #[inline(always)]
    fn read() -> u32 {
        let w: u32;
        unsafe { core::arch::asm!("csrrw {0}, 0x7c0, x0", out(reg) w, options(nostack)) }
        w
    }

    /// Asks for `tag` on the value at `operand` and reads the eight answer
    /// words into `dst`, which may be the operand: the host has read it by
    /// then.
    #[inline(always)]
    unsafe fn query<T: ?Sized>(tag: u32, operand: *const T, dst: *mut [u32; 8]) {
        write(tag);
        write(operand.cast::<u8>() as usize as u32);
        let dst = dst.cast::<u32>();
        for i in 0..8 {
            dst.add(i).write(read());
        }
    }

    /// Whether the words at `x` are below `modulus`: subtracting it borrows
    /// exactly then, and adding it back restores them.
    #[inline(always)]
    unsafe fn below(x: *mut [u32; 8], modulus: &'static Operand) -> bool {
        let m = core::ptr::from_ref(modulus).cast::<()>();
        let borrow = bigint_op_delegation_raw(x.cast(), m, BigIntOps::Sub) != 0;
        bigint_op_delegation_raw(x.cast(), m, BigIntOps::Add);
        borrow
    }

    pub struct HostHints;

    impl Secp256k1Hooks for HostHints {
        const FE_INVERT_IS_CHEAP: bool = true;
        const FE_DIVIDE_IS_CHEAP: bool = true;

        /// The quotient as the host gives it: any 256-bit representative is
        /// the element, since the check is modulo p.
        fn fe_divide<'q>(
            &mut self,
            fraction: &mut [FieldElement; 2],
            quotient: &'q mut MaybeUninit<FieldElement>,
        ) -> &'q mut FieldElement {
            // SAFETY: the element is its eight words (checked above), any
            // value of which is an element
            let quotient = unsafe {
                query(DIVIDE, fraction, quotient.as_mut_ptr().cast());
                quotient.assume_init_mut()
            };
            // quotient · denominator = numerator; the denominator is not zero
            // (the caller's obligation), so only the quotient passes
            let [numerator, denominator] = fraction;
            denominator.mul_in_place(quotient);
            denominator.sub_in_place(numerator);
            assert!(denominator.is_zero());
            quotient
        }

        fn fe_sqrt_and_assign(&mut self, x: &mut FieldElement) -> bool {
            // as the default hook: the root of 0 is 0
            if x.is_zero() {
                return true;
            }
            let operand = *x;
            let x_words = core::ptr::from_mut(x).cast::<[u32; 8]>();
            // SAFETY: as in fe_divide; x is 32-byte aligned
            let not_square = unsafe {
                query(SQRT, x_words, x_words);
                let not_square = read() != 0;
                assert!(below(x_words, &P));
                not_square
            };
            // p = 3 mod 4: x^((p+1)/4) squared is x for a square, else -x
            let mut squared = *x;
            squared.square_in_place();
            if not_square {
                squared.add_in_place(&operand);
            } else {
                squared.sub_in_place(&operand);
            }
            assert!(squared.is_zero());
            !not_square
        }

        fn fe_invert_and_assign(&mut self, x: &mut FieldElement) {
            // as the default hook: the inverse of 0 is 0
            if x.is_zero() {
                return;
            }
            let mut product = *x;
            let x_words = core::ptr::from_mut(x).cast::<[u32; 8]>();
            // SAFETY: as in fe_sqrt_and_assign
            unsafe {
                query(INVERT, x_words, x_words);
                assert!(below(x_words, &P));
            }
            product.mul_in_place(x);
            assert!(product.is_one());
        }

        fn scalar_invert_and_assign(&mut self, x: &mut Scalar) {
            if x.is_zero() {
                return;
            }
            let mut product = *x;
            let x_words = core::ptr::from_mut(x).cast::<[u32; 8]>();
            // SAFETY: as in fe_sqrt_and_assign
            unsafe {
                query(SCALAR_INVERT, x_words, x_words);
                assert!(below(x_words, &N));
            }
            product *= &*x;
            assert!(product.is_one());
        }
    }
}

/// The hinted recovery against the default hooks' (inversions and square roots
/// by exponentiation, Jacobian coordinates), as ZKsync OS's
/// `test_advice_matches_no_advice` checks its oracle's: random inputs (about
/// half have an `r` on the curve and recover some key), the edge values of
/// `r` and `s`, the generator's `x` as `r` (the affine formulas' doubling and
/// infinity cases) and ZKsync OS's regression inputs. The output words are
/// the cases, the disagreements, the keys recovered and the first
/// disagreement.
#[cfg(feature = "ecrecover-selftest")]
mod selftest {
    use super::hints::HostHints;
    use airbender_crypto::secp256k1::hooks::DefaultSecp256k1Hooks;
    use airbender_crypto::secp256k1::recover_from_bytes_with_hooks;

    extern "C" {
        fn write_output(output: *const u8, size: usize);
    }

    const GX: [u8; 32] = [
        0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87, 0x0b,
        0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16, 0xf8,
        0x17, 0x98,
    ];
    const N: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xfe, 0xba, 0xae, 0xdc, 0xe6, 0xaf, 0x48, 0xa0, 0x3b, 0xbf, 0xd2, 0x5e, 0x8c, 0xd0, 0x36,
        0x41, 0x41,
    ];

    fn hex32(s: &str) -> [u8; 32] {
        let mut out = [0u8; 32];
        for (i, byte) in out.iter_mut().enumerate() {
            *byte = u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap();
        }
        out
    }

    /// digest, v, r, s of ZKsync OS's ecrecover tests (basic_system ecrecover.rs)
    const REGRESSIONS: [[&str; 4]; 4] = [
        [
            "38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e",
            "1b",
            "38d18acb67d25c8bb9942764b62f18e17054f66a817bd4295423adf9ed98873e",
            "789d1dd423d25f0772d2748d60f7e4b81bb14d086eba8e8e8efb6dcff8a4ae02",
        ],
        [
            "6b8d2c81b11b2d699528dde488dbdf2f94293d0d33c32e347f255fa4a6c1f0a9",
            "1b",
            "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
            "6b8d2c81b11b2d699528dde488dbdf2f94293d0d33c32e347f255fa4a6c1f0a9",
        ],
        [
            "00c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c",
            "1c",
            "00b1693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75f",
            "00b940b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549",
        ],
        [
            "22bd0731d4bffa88402625b5ba39e04ee9add6534c31da6c119d825a39822b29",
            "1c",
            "66667463d40ac441662188ed3e66329c21aca165133392cc1a14b84485600a87",
            "5087ffc16905cc6ceaef174630ce9dd0c40b3f4e94ff00ee3658a6a67fec2613",
        ],
    ];

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn bytes(&mut self) -> [u8; 32] {
            let mut out = [0u8; 32];
            for chunk in out.chunks_mut(8) {
                chunk.copy_from_slice(&self.next().to_be_bytes());
            }
            out
        }

        /// Random, or one of the edges: 0, 1, n - 1, n, 2^256 - 1, Gx
        fn value(&mut self) -> [u8; 32] {
            let pick = self.next() % 16;
            let mut x = self.bytes();
            match pick {
                0 => x = [0; 32],
                1 => x = [0; 32].tap_last(1),
                2 => x = N.tap_last(N[31] - 1),
                3 => x = N,
                4 => x = [0xff; 32],
                5 => x = GX,
                6 => x[..16].fill(0), // small
                _ => {}
            }
            x
        }
    }

    trait TapLast {
        fn tap_last(self, last: u8) -> Self;
    }

    impl TapLast for [u8; 32] {
        fn tap_last(mut self, last: u8) -> Self {
            self[31] = last;
            self
        }
    }

    fn recover(
        digest: &[u8; 32],
        r: &[u8; 32],
        s: &[u8; 32],
        odd: bool,
        hinted: bool,
    ) -> Option<[u8; 64]> {
        let result = if hinted {
            recover_from_bytes_with_hooks(digest, r, s, odd, &mut HostHints)
        } else {
            recover_from_bytes_with_hooks(digest, r, s, odd, &mut DefaultSecp256k1Hooks)
        };
        result.ok().map(|point| {
            let mut out = [0u8; 64];
            let (x, y) = out.split_at_mut(32);
            point.write_coordinates(x.try_into().unwrap(), y.try_into().unwrap());
            out
        })
    }

    #[no_mangle]
    pub extern "C" fn monad_zkvm_execute_witness() {
        let mut rng = Rng(0x243f_6a88_85a3_08d3);
        let (mut cases, mut failures, mut recovered, mut first) = (0u32, 0u32, 0u32, u32::MAX);
        let mut check = |digest: &[u8; 32], r: &[u8; 32], s: &[u8; 32], odd: bool| {
            let hinted = recover(digest, r, s, odd, true);
            if hinted != recover(digest, r, s, odd, false) {
                if failures == 0 {
                    first = cases;
                }
                failures += 1;
            }
            recovered += u32::from(hinted.is_some());
            cases += 1;
        };
        for [digest, v, r, s] in REGRESSIONS {
            check(&hex32(digest), &hex32(r), &hex32(s), v == "1c");
        }
        for i in 0..1200u32 {
            let (digest, s) = (rng.value(), rng.value());
            // a third with the generator's x as r: R = G or -G
            let r = if i % 3 == 0 { GX } else { rng.value() };
            let odd = rng.next() & 1 == 1;
            check(&digest, &r, &s, odd);
        }
        let out = [cases, failures, recovered, first];
        unsafe { write_output(out.as_ptr().cast(), core::mem::size_of_val(&out)) };
    }
}

/// ecrecover's public key, x || y big-endian. `recid` is the parity of y;
/// Ethereum never recovers from an `r` reduced past the group order.
#[no_mangle]
pub unsafe extern "C" fn zkvm_secp256k1_ecrecover(
    msg: *const [u8; 32],
    sig: *const [u8; 64],
    recid: u8,
    output: *mut [u8; 64],
) -> i32 {
    if recid > 1 {
        return ZKVM_EFAIL;
    }
    let sig = &*sig;
    let (r, s) = sig.split_at(32);
    let (r, s): (&[u8; 32], &[u8; 32]) = (r.try_into().unwrap(), s.try_into().unwrap());
    match recover_from_bytes_with_hooks(&*msg, r, s, recid == 1, &mut hints::HostHints) {
        Ok(point) => {
            let (x, y) = (*output).split_at_mut(32);
            point.write_coordinates(x.try_into().unwrap(), y.try_into().unwrap());
            ZKVM_EOK
        }
        Err(_) => ZKVM_EFAIL,
    }
}

#[no_mangle]
pub unsafe extern "C" fn zkvm_sha256(data: *const u8, len: usize, output: *mut [u8; 32]) -> i32 {
    use airbender_crypto::sha256::Digest as _;
    let input = core::slice::from_raw_parts(data, len);
    (*output).copy_from_slice(&Sha256::digest(input));
    ZKVM_EOK
}

/// The 20-byte digest right-aligned, after 12 zero bytes, as the precompile
/// returns it (and as ZisK's accelerator writes it).
#[no_mangle]
pub unsafe extern "C" fn zkvm_ripemd160(data: *const u8, len: usize, output: *mut [u8; 32]) -> i32 {
    let input = core::slice::from_raw_parts(data, len);
    let out = &mut *output;
    out[..12].fill(0);
    out[12..].copy_from_slice(&Ripemd160::digest(input));
    ZKVM_EOK
}

// ---- BN254 (EIP-196/197) ----
// After ZKsync OS's bn254_ecadd/ecmul/pairing_check without an oracle:
// canonical coordinates, (0, 0) for infinity, G2 with the imaginary parts
// first, on-curve and (for G2) subgroup checks.
mod bn254 {
    use super::{ZKVM_EFAIL, ZKVM_EOK};
    use airbender_crypto::ark_ec::pairing::Pairing;
    use airbender_crypto::ark_ec::{AffineRepr, CurveGroup};
    use airbender_crypto::ark_ff::{One, PrimeField, Zero};
    use airbender_crypto::ark_serialize::Valid;
    use airbender_crypto::bn254::curves::Bn254;
    use airbender_crypto::bn254::{Fq, Fq2, G1Affine, G2Affine};
    use alloc::vec::Vec;

    type BigInt = <Fq as PrimeField>::BigInt;

    pub fn bigint_from_be(bytes: &[u8; 32]) -> BigInt {
        let mut limbs = [0u64; 4];
        for (i, limb) in limbs.iter_mut().enumerate() {
            let off = 24 - 8 * i;
            *limb = u64::from_be_bytes(bytes[off..off + 8].try_into().unwrap());
        }
        BigInt::new(limbs)
    }

    fn write_be(value: &BigInt, out: &mut [u8]) {
        for i in 0..4 {
            let off = 24 - 8 * i;
            out[off..off + 8].copy_from_slice(&value.0[i].to_be_bytes());
        }
    }

    fn parse_fq(bytes: &[u8]) -> Option<Fq> {
        Fq::from_bigint(bigint_from_be(bytes.try_into().unwrap()))
    }

    fn parse_g1(bytes: &[u8; 64]) -> Option<G1Affine> {
        if bytes.iter().all(|b| *b == 0) {
            return Some(G1Affine::identity());
        }
        let point = G1Affine::new_unchecked(parse_fq(&bytes[..32])?, parse_fq(&bytes[32..])?);
        point.check().ok()?;
        Some(point)
    }

    fn write_g1(point: &G1Affine, out: &mut [u8; 64]) {
        match point.xy() {
            Some((x, y)) => {
                write_be(&x.into_bigint(), &mut out[..32]);
                write_be(&y.into_bigint(), &mut out[32..]);
            }
            None => out.fill(0),
        }
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bn254_g1_add(
        p1: *const [u8; 64],
        p2: *const [u8; 64],
        result: *mut [u8; 64],
    ) -> i32 {
        let (Some(a), Some(b)) = (parse_g1(&*p1), parse_g1(&*p2)) else {
            return ZKVM_EFAIL;
        };
        let sum = airbender_crypto::bn254::g1::add_affine(&a, &b).into_affine();
        write_g1(&sum, &mut *result);
        ZKVM_EOK
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bn254_g1_mul(
        point: *const [u8; 64],
        scalar: *const [u8; 32],
        result: *mut [u8; 64],
    ) -> i32 {
        let Some(p) = parse_g1(&*point) else {
            return ZKVM_EFAIL;
        };
        if p.is_zero() {
            (*result).fill(0);
            return ZKVM_EOK;
        }
        // any 256-bit integer multiplies; no reduction
        let product = p.mul_bigint(bigint_from_be(&*scalar)).into_affine();
        write_g1(&product, &mut *result);
        ZKVM_EOK
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bn254_pairing(
        pairs: *const [u8; 192],
        num_pairs: usize,
        verified: *mut bool,
    ) -> i32 {
        let input = core::slice::from_raw_parts(pairs, num_pairs);
        let mut g1s = Vec::with_capacity(num_pairs);
        let mut g2s = Vec::with_capacity(num_pairs);
        for pair in input {
            let (Some(g1_x), Some(g1_y)) = (parse_fq(&pair[0..32]), parse_fq(&pair[32..64])) else {
                return ZKVM_EFAIL;
            };
            let g1_is_zero = g1_x.is_zero() && g1_y.is_zero();
            let g1 = G1Affine::new_unchecked(g1_x, g1_y);
            if !g1_is_zero && g1.check().is_err() {
                return ZKVM_EFAIL;
            }
            // imaginary parts first
            let (Some(x1), Some(x0), Some(y1), Some(y0)) = (
                parse_fq(&pair[64..96]),
                parse_fq(&pair[96..128]),
                parse_fq(&pair[128..160]),
                parse_fq(&pair[160..192]),
            ) else {
                return ZKVM_EFAIL;
            };
            let (x, y) = (Fq2::new(x0, x1), Fq2::new(y0, y1));
            if x.is_zero() && y.is_zero() {
                continue; // e(P, O) = 1
            }
            let g2 = G2Affine::new_unchecked(x, y);
            if !g2.is_on_curve() || !g2.is_in_correct_subgroup_assuming_on_curve() {
                return ZKVM_EFAIL;
            }
            if g1_is_zero {
                continue; // e(O, Q) = 1
            }
            g1s.push(g1);
            g2s.push(g2);
        }
        *verified = if g1s.is_empty() {
            true
        } else {
            let miller = Bn254::multi_miller_loop(g1s.iter(), g2s.iter());
            match Bn254::final_exponentiation(miller) {
                Some(gt) => gt.0.is_one(),
                None => return ZKVM_EFAIL,
            }
        };
        ZKVM_EOK
    }
}

// ---- BLS12-381 (EIP-2537) and KZG (EIP-4844) ----
// Points arrive raw: 48-byte big-endian coordinates, Fp2 as c0 || c1, all
// zero for infinity. airbender-crypto's eip2537 helpers take the EVM's
// 64-byte padded elements, so the coordinates are padded on the way in.
mod bls {
    use super::{ZKVM_EFAIL, ZKVM_EOK};
    use airbender_crypto::ark_ec::pairing::Pairing;
    use airbender_crypto::ark_ec::{AffineRepr, CurveGroup};
    use airbender_crypto::ark_ff::{Field, PrimeField, Zero};
    use airbender_crypto::ark_serialize::CanonicalDeserialize;
    use airbender_crypto::bls12_381::curves::Bls12_381;
    use airbender_crypto::bls12_381::{eip2537, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
    use alloc::vec::Vec;

    fn pad(raw: &[u8], out: &mut [u8]) {
        // raw is a run of 48-byte elements, out the same run of 64-byte ones
        for (r, o) in raw.chunks_exact(48).zip(out.chunks_exact_mut(64)) {
            o[..16].fill(0);
            o[16..].copy_from_slice(r);
        }
    }

    fn unpad(padded: &[u8], out: &mut [u8]) {
        for (p, o) in padded.chunks_exact(64).zip(out.chunks_exact_mut(48)) {
            o.copy_from_slice(&p[16..]);
        }
    }

    fn parse_g1(raw: &[u8; 96], subgroup: bool) -> Option<G1Affine> {
        let mut p = [0u8; 128];
        pad(raw, &mut p);
        let (point, _) = eip2537::parse_g1_bytes(&p)?;
        (!subgroup || point.is_zero() || point.is_in_correct_subgroup_assuming_on_curve())
            .then_some(point)
    }

    fn parse_g2(raw: &[u8; 192], subgroup: bool) -> Option<G2Affine> {
        let mut p = [0u8; 256];
        pad(raw, &mut p);
        let (point, _) = eip2537::parse_g2_bytes(&p)?;
        (!subgroup || point.is_zero() || point.is_in_correct_subgroup_assuming_on_curve())
            .then_some(point)
    }

    fn write_g1(point: G1Affine, out: &mut [u8; 96]) {
        let mut p = [0u8; 128];
        eip2537::serialize_g1_bytes(point, &mut p);
        unpad(&p, out);
    }

    fn write_g2(point: G2Affine, out: &mut [u8; 192]) {
        let mut p = [0u8; 256];
        eip2537::serialize_g2_bytes(point, &mut p);
        unpad(&p, out);
    }

    fn scalar(bytes: &[u8; 32]) -> <Fr as PrimeField>::BigInt {
        airbender_crypto::parse_u256_be(bytes)
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_g1_add(
        p1: *const [u8; 96],
        p2: *const [u8; 96],
        result: *mut [u8; 96],
    ) -> i32 {
        let (Some(a), Some(b)) = (parse_g1(&*p1, false), parse_g1(&*p2, false)) else {
            return ZKVM_EFAIL;
        };
        write_g1((a + b).into_affine(), &mut *result);
        ZKVM_EOK
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_g2_add(
        p1: *const [u8; 192],
        p2: *const [u8; 192],
        result: *mut [u8; 192],
    ) -> i32 {
        let (Some(a), Some(b)) = (parse_g2(&*p1, false), parse_g2(&*p2, false)) else {
            return ZKVM_EFAIL;
        };
        write_g2((a + b).into_affine(), &mut *result);
        ZKVM_EOK
    }

    /// pairs: num_pairs x (96-byte point, 32-byte scalar)
    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_g1_msm(
        pairs: *const [u8; 128],
        num_pairs: usize,
        result: *mut [u8; 96],
    ) -> i32 {
        let mut acc = G1Projective::zero();
        for pair in core::slice::from_raw_parts(pairs, num_pairs) {
            let Some(point) = parse_g1(pair[..96].try_into().unwrap(), true) else {
                return ZKVM_EFAIL;
            };
            acc += point.mul_bigint(scalar(pair[96..].try_into().unwrap()));
        }
        write_g1(acc.into_affine(), &mut *result);
        ZKVM_EOK
    }

    /// pairs: num_pairs x (192-byte point, 32-byte scalar)
    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_g2_msm(
        pairs: *const [u8; 224],
        num_pairs: usize,
        result: *mut [u8; 192],
    ) -> i32 {
        let mut acc = G2Projective::zero();
        for pair in core::slice::from_raw_parts(pairs, num_pairs) {
            let Some(point) = parse_g2(pair[..192].try_into().unwrap(), true) else {
                return ZKVM_EFAIL;
            };
            acc += point.mul_bigint(scalar(pair[192..].try_into().unwrap()));
        }
        write_g2(acc.into_affine(), &mut *result);
        ZKVM_EOK
    }

    /// pairs: num_pairs x (96-byte G1, 192-byte G2)
    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_pairing(
        pairs: *const [u8; 288],
        num_pairs: usize,
        verified: *mut bool,
    ) -> i32 {
        let mut g1s = Vec::with_capacity(num_pairs);
        let mut g2s = Vec::with_capacity(num_pairs);
        for pair in core::slice::from_raw_parts(pairs, num_pairs) {
            let (Some(g1), Some(g2)) = (
                parse_g1(pair[..96].try_into().unwrap(), true),
                parse_g2(pair[96..].try_into().unwrap(), true),
            ) else {
                return ZKVM_EFAIL;
            };
            g1s.push(g1);
            g2s.push(g2);
        }
        let gt = Bls12_381::multi_pairing(g1s, g2s);
        *verified = gt.0 == <Bls12_381 as Pairing>::TargetField::ONE;
        ZKVM_EOK
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_map_fp_to_g1(
        element: *const [u8; 48],
        result: *mut [u8; 96],
    ) -> i32 {
        let mut p = [0u8; 64];
        pad(&*element, &mut p);
        let Some(fe) = eip2537::parse_fq_bytes(&p) else {
            return ZKVM_EFAIL;
        };
        let Ok(point) = eip2537::map_fp_to_g1(fe) else {
            return ZKVM_EFAIL;
        };
        write_g1(point.clear_cofactor(), &mut *result);
        ZKVM_EOK
    }

    #[no_mangle]
    pub unsafe extern "C" fn zkvm_bls12_map_fp2_to_g2(
        element: *const [u8; 96],
        result: *mut [u8; 192],
    ) -> i32 {
        let mut p = [0u8; 128];
        pad(&*element, &mut p);
        let Some(fe) = eip2537::parse_fq2_bytes(&p) else {
            return ZKVM_EFAIL;
        };
        let Ok(point) = eip2537::map_fp2_to_g2(fe) else {
            return ZKVM_EFAIL;
        };
        write_g2(point.clear_cofactor(), &mut *result);
        ZKVM_EOK
    }

    /// EIP-4844's point evaluation: compressed G1 commitment and proof, z and y
    /// canonical scalars. The versioned hash is checked by the caller.
    #[no_mangle]
    pub unsafe extern "C" fn zkvm_kzg_point_eval(
        commitment: *const [u8; 48],
        z: *const [u8; 32],
        y: *const [u8; 32],
        proof: *const [u8; 48],
        verified: *mut bool,
    ) -> i32 {
        let (z, y) = (scalar(&*z), scalar(&*y));
        if z >= Fr::MODULUS || y >= Fr::MODULUS {
            return ZKVM_EFAIL;
        }
        let (commitment, proof): (&[u8; 48], &[u8; 48]) = (&*commitment, &*proof);
        let (Ok(c), Ok(p)) = (
            G1Affine::deserialize_compressed(&commitment[..]),
            G1Affine::deserialize_compressed(&proof[..]),
        ) else {
            return ZKVM_EFAIL;
        };
        *verified = airbender_crypto::bls12_381::verify_kzg_proof(c, p, z, y);
        ZKVM_EOK
    }
}

// ---- P-256 (EIP-7951) ----
#[no_mangle]
pub unsafe extern "C" fn zkvm_secp256r1_verify(
    msg: *const [u8; 32],
    sig: *const [u8; 64],
    pubkey: *const [u8; 64],
    verified: *mut bool,
) -> i32 {
    let (sig, pk) = (&*sig, &*pubkey);
    let r: &[u8; 32] = sig[..32].try_into().unwrap();
    let s: &[u8; 32] = sig[32..].try_into().unwrap();
    let x: &[u8; 32] = pk[..32].try_into().unwrap();
    let y: &[u8; 32] = pk[32..].try_into().unwrap();
    // an invalid signature or key is a failed verification, as the precompile
    // answers both with empty output
    *verified = airbender_crypto::secp256r1::verify(&*msg, r, s, x, y).unwrap_or(false);
    ZKVM_EOK
}

// ---- modexp (EIP-198) ----
// num-bigint for now: ZKsync OS's delegation-backed modexp needs its oracle.
#[no_mangle]
pub unsafe extern "C" fn zkvm_modexp(
    base: *const u8,
    base_len: usize,
    exp: *const u8,
    exp_len: usize,
    modulus: *const u8,
    mod_len: usize,
    output: *mut u8,
) -> i32 {
    use num_bigint::BigUint;
    use num_traits::Zero;
    if mod_len == 0 {
        return ZKVM_EOK;
    }
    let bytes = |p: *const u8, n: usize| if n == 0 { &[][..] } else { core::slice::from_raw_parts(p, n) };
    let out = core::slice::from_raw_parts_mut(output, mod_len);
    out.fill(0);
    let m = BigUint::from_bytes_be(bytes(modulus, mod_len));
    if m.is_zero() {
        return ZKVM_EOK;
    }
    let r = BigUint::from_bytes_be(bytes(base, base_len))
        .modpow(&BigUint::from_bytes_be(bytes(exp, exp_len)), &m)
        .to_bytes_be();
    if !(r.len() == 1 && r[0] == 0) {
        out[mod_len - r.len()..].copy_from_slice(&r);
    }
    ZKVM_EOK
}

// ---- BLAKE2 F (EIP-152) ----
#[no_mangle]
pub unsafe extern "C" fn zkvm_blake2f(
    rounds: u32,
    h: *mut [u8; 64],
    m: *const [u8; 128],
    t: *const [u8; 16],
    f: u8,
) -> i32 {
    const IV: [u64; 8] = [
        0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
        0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
    ];
    const SIGMA: [[usize; 16]; 10] = [
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
        [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
        [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
        [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
        [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
        [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
        [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
        [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
        [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
        [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    ];
    let word = |b: &[u8], i: usize| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
    let (hb, mb, tb) = (&mut *h, &*m, &*t);
    let mut hv = [0u64; 8];
    for (i, w) in hv.iter_mut().enumerate() {
        *w = word(hb, i);
    }
    let mut mw = [0u64; 16];
    for (i, w) in mw.iter_mut().enumerate() {
        *w = word(mb, i);
    }
    let mut v = [0u64; 16];
    v[..8].copy_from_slice(&hv);
    v[8..].copy_from_slice(&IV);
    v[12] ^= word(tb, 0);
    v[13] ^= word(tb, 1);
    if f != 0 {
        v[14] = !v[14];
    }
    #[inline(always)]
    fn g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
        v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
        v[d] = (v[d] ^ v[a]).rotate_right(32);
        v[c] = v[c].wrapping_add(v[d]);
        v[b] = (v[b] ^ v[c]).rotate_right(24);
        v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
        v[d] = (v[d] ^ v[a]).rotate_right(16);
        v[c] = v[c].wrapping_add(v[d]);
        v[b] = (v[b] ^ v[c]).rotate_right(63);
    }
    for r in 0..rounds as usize {
        let s = &SIGMA[r % 10];
        g(&mut v, 0, 4, 8, 12, mw[s[0]], mw[s[1]]);
        g(&mut v, 1, 5, 9, 13, mw[s[2]], mw[s[3]]);
        g(&mut v, 2, 6, 10, 14, mw[s[4]], mw[s[5]]);
        g(&mut v, 3, 7, 11, 15, mw[s[6]], mw[s[7]]);
        g(&mut v, 0, 5, 10, 15, mw[s[8]], mw[s[9]]);
        g(&mut v, 1, 6, 11, 12, mw[s[10]], mw[s[11]]);
        g(&mut v, 2, 7, 8, 13, mw[s[12]], mw[s[13]]);
        g(&mut v, 3, 4, 9, 14, mw[s[14]], mw[s[15]]);
    }
    for i in 0..8 {
        hb[8 * i..8 * i + 8].copy_from_slice(&(hv[i] ^ v[i] ^ v[i + 8]).to_le_bytes());
    }
    ZKVM_EOK
}
