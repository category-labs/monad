//! The host's half of the guest's 4-dimensional GLV ecrecover check
//! (airbender-crypto secp256k1/recover_glv4.rs): the recovered key
//! `Q = na·R + ng·G`, and a short `(k0, k1, m0, m1)` with
//! `(k0 + k1·λ)·na ≡ m0 + m1·λ (mod n)`, from the 4-dimensional lattice of
//! such vectors, LLL-reduced. Its determinant is `n`, so the reduced basis's
//! first vector has coordinates near `n^(1/4)`, about 2^64: the guest then
//! checks `k·Q - (k·na)·R - (k·ng)·G = O` for `k = k0 + k1·λ` with scalars of
//! 64 bits where the recovery's own has 128.

use num_bigint::{BigInt, BigUint, Sign};
use num_traits_shim::*;

/// The few num-traits methods used here, without the dependency.
mod num_traits_shim {
    use num_bigint::{BigInt, BigUint};
    pub fn zero() -> BigInt {
        BigInt::from(0)
    }
    pub fn is_zero_u(x: &BigUint) -> bool {
        x.bits() == 0
    }
}

fn hex(s: &str) -> BigUint {
    BigUint::parse_bytes(s.as_bytes(), 16).unwrap()
}

pub struct Curve {
    pub p: BigUint,
    pub n: BigUint,
    g: (BigUint, BigUint),
    lambda: BigUint,
}

/// A point in Jacobian coordinates; z = 0 is the point at infinity.
#[derive(Clone)]
struct Jac {
    x: BigUint,
    y: BigUint,
    z: BigUint,
}

impl Curve {
    pub fn secp256k1() -> Self {
        Self {
            p: hex("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f"),
            n: hex("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141"),
            g: (
                hex("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"),
                hex("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8"),
            ),
            lambda: hex("5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72"),
        }
    }

    fn sub(&self, a: &BigUint, b: &BigUint) -> BigUint {
        (a + &self.p - b) % &self.p
    }

    fn mul(&self, a: &BigUint, b: &BigUint) -> BigUint {
        a * b % &self.p
    }

    fn double(&self, a: &Jac) -> Jac {
        if is_zero_u(&a.z) || is_zero_u(&a.y) {
            return Jac { x: 0u32.into(), y: 1u32.into(), z: 0u32.into() };
        }
        let aa = self.mul(&a.x, &a.x);
        let b = self.mul(&a.y, &a.y);
        let c = self.mul(&b, &b);
        let xb = (&a.x + &b) % &self.p;
        let d = self.sub(&self.sub(&self.mul(&xb, &xb), &aa), &c);
        let d = (d * 2u32) % &self.p;
        let e = (aa * 3u32) % &self.p;
        let f = self.mul(&e, &e);
        let x3 = self.sub(&f, &((&d * 2u32) % &self.p));
        let y3 = self.sub(&self.mul(&e, &self.sub(&d, &x3)), &((c * 8u32) % &self.p));
        let z3 = (self.mul(&a.y, &a.z) * 2u32) % &self.p;
        Jac { x: x3, y: y3, z: z3 }
    }

    fn add(&self, a: &Jac, b: &Jac) -> Jac {
        if is_zero_u(&a.z) {
            return b.clone();
        }
        if is_zero_u(&b.z) {
            return a.clone();
        }
        let z1z1 = self.mul(&a.z, &a.z);
        let z2z2 = self.mul(&b.z, &b.z);
        let u1 = self.mul(&a.x, &z2z2);
        let u2 = self.mul(&b.x, &z1z1);
        let s1 = self.mul(&self.mul(&a.y, &b.z), &z2z2);
        let s2 = self.mul(&self.mul(&b.y, &a.z), &z1z1);
        if u1 == u2 {
            if s1 == s2 {
                return self.double(a);
            }
            return Jac { x: 0u32.into(), y: 1u32.into(), z: 0u32.into() };
        }
        let h = self.sub(&u2, &u1);
        let i = {
            let h2 = (&h * 2u32) % &self.p;
            self.mul(&h2, &h2)
        };
        let j = self.mul(&h, &i);
        let r = (self.sub(&s2, &s1) * 2u32) % &self.p;
        let v = self.mul(&u1, &i);
        let x3 = self.sub(&self.sub(&self.mul(&r, &r), &j), &((&v * 2u32) % &self.p));
        let y3 = self.sub(&self.mul(&r, &self.sub(&v, &x3)), &((self.mul(&s1, &j) * 2u32) % &self.p));
        let zz = (&a.z + &b.z) % &self.p;
        let z3 = self.mul(&self.sub(&self.sub(&self.mul(&zz, &zz), &z1z1), &z2z2), &h);
        Jac { x: x3, y: y3, z: z3 }
    }

    /// a·P + b·Q by one ladder over both scalars' bits
    fn mul2(&self, a: &BigUint, p: &Jac, b: &BigUint, q: &Jac) -> Jac {
        let pq = self.add(p, q);
        let mut r = Jac { x: 0u32.into(), y: 1u32.into(), z: 0u32.into() };
        let bits = a.bits().max(b.bits());
        for i in (0..bits).rev() {
            r = self.double(&r);
            match (a.bit(i), b.bit(i)) {
                (true, true) => r = self.add(&r, &pq),
                (true, false) => r = self.add(&r, p),
                (false, true) => r = self.add(&r, q),
                _ => {}
            }
        }
        r
    }

    fn affine(&self, a: &Jac) -> Option<(BigUint, BigUint)> {
        if is_zero_u(&a.z) {
            return None;
        }
        let zi = a.z.modinv(&self.p).unwrap();
        let zi2 = self.mul(&zi, &zi);
        Some((self.mul(&a.x, &zi2), self.mul(&self.mul(&a.y, &zi2), &zi)))
    }

    /// `na·R + ng·G` in affine coordinates, `None` for the point at infinity
    pub fn recover(&self, r: &(BigUint, BigUint), na: &BigUint, ng: &BigUint) -> Option<(BigUint, BigUint)> {
        let one = BigUint::from(1u32);
        let rj = Jac { x: r.0.clone(), y: r.1.clone(), z: one.clone() };
        let gj = Jac { x: self.g.0.clone(), y: self.g.1.clone(), z: one };
        self.affine(&self.mul2(na, &rj, ng, &gj))
    }

    /// A short `(k0, k1, m0, m1)` with `(k0 + k1·λ)·na ≡ m0 + m1·λ (mod n)`
    /// and `(k0, k1) ≠ 0`: the shortest vector of the reduced basis of
    /// `(1, 0, na, 0), (0, 1, λ·na, 0), (0, 0, n, 0), (0, 0, -λ, 1)`.
    pub fn short_multiple(&self, na: &BigUint) -> [BigInt; 4] {
        let n = BigInt::from_biguint(Sign::Plus, self.n.clone());
        let na_i = BigInt::from_biguint(Sign::Plus, na.clone());
        let lam = BigInt::from_biguint(Sign::Plus, self.lambda.clone());
        let lam_na = (&lam * &na_i) % &n;
        let minus_lam = (&n - &lam) % &n;
        let mut b: Vec<[BigInt; 4]> = vec![
            [1.into(), zero(), na_i.clone(), zero()],
            [zero(), 1.into(), lam_na, zero()],
            [zero(), zero(), n.clone(), zero()],
            [zero(), zero(), minus_lam, 1.into()],
        ];
        lll(&mut b);
        let maxabs = |v: &[BigInt; 4]| v.iter().map(|x| x.magnitude().clone()).max().unwrap();
        let mut best: Option<[BigInt; 4]> = None;
        for v in &b {
            if v[0] == zero() && v[1] == zero() {
                continue;
            }
            if best.as_ref().map_or(true, |w| maxabs(v) < maxabs(w)) {
                best = Some(v.clone());
            }
        }
        let v = best.expect("a lattice vector with k != 0");
        // the relation, checked here too
        let k = (&v[0] + &v[1] * &lam) % &n;
        let m = (&v[2] + &v[3] * &lam) % &n;
        let lhs = ((k * &na_i - m) % &n + &n) % &n;
        assert_eq!(lhs, zero(), "short multiple relation");
        v
    }
}

fn dot(a: &[BigInt; 4], b: &[BigInt; 4]) -> BigInt {
    a.iter().zip(b).map(|(x, y)| x * y).sum()
}

/// Rounded quotient a / b for b > 0
fn round_div(a: &BigInt, b: &BigInt) -> BigInt {
    let two = BigInt::from(2);
    let num = a * &two + b;
    let den = b * &two;
    // floor division for signed numerators
    let (q, r) = (&num / &den, &num % &den);
    if r.sign() == Sign::Minus { q - 1 } else { q }
}

/// Integral LLL (Cohen, Algorithm 2.6.7) with δ = 3/4, rows in place.
fn lll(b: &mut Vec<[BigInt; 4]>) {
    let dim = b.len();
    // 1-based arrays as in Cohen
    let mut d: Vec<BigInt> = vec![zero(); dim + 1];
    let mut lam: Vec<Vec<BigInt>> = vec![vec![zero(); dim + 1]; dim + 1];
    d[0] = 1.into();
    d[1] = dot(&b[0], &b[0]);
    let mut k = 2usize;
    let mut kmax = 1usize;
    let red = |b: &mut Vec<[BigInt; 4]>, lam: &mut Vec<Vec<BigInt>>, d: &Vec<BigInt>, k: usize, l: usize| {
        if (&lam[k][l] * BigInt::from(2)).magnitude() > d[l].magnitude() {
            let q = round_div(&lam[k][l], &d[l]);
            let bl = b[l - 1].clone();
            for c in 0..4 {
                b[k - 1][c] -= &q * &bl[c];
            }
            lam[k][l] -= &q * &d[l];
            for i in 1..l {
                let t = &q * &lam[l][i];
                lam[k][i] -= t;
            }
        }
    };
    while k <= dim {
        if k > kmax {
            kmax = k;
            for j in 1..=k {
                let mut u = dot(&b[k - 1], &b[j - 1]);
                for i in 1..j {
                    u = (&d[i] * &u - &lam[k][i] * &lam[j][i]) / &d[i - 1];
                }
                if j < k {
                    lam[k][j] = u;
                } else {
                    assert!(u != zero(), "dependent basis");
                    d[k] = u;
                }
            }
        }
        red(b, &mut lam, &d, k, k - 1);
        let lhs = BigInt::from(4) * &d[k] * &d[k - 2];
        let rhs = BigInt::from(3) * &d[k - 1] * &d[k - 1] - BigInt::from(4) * &lam[k][k - 1] * &lam[k][k - 1];
        if lhs < rhs {
            // SWAP(k)
            b.swap(k - 1, k - 2);
            for j in 1..k - 1 {
                let t = lam[k][j].clone();
                lam[k][j] = lam[k - 1][j].clone();
                lam[k - 1][j] = t;
            }
            let l = lam[k][k - 1].clone();
            let bb = (&d[k - 2] * &d[k] + &l * &l) / &d[k - 1];
            for i in k + 1..=kmax {
                let t = lam[i][k].clone();
                lam[i][k] = (&d[k] * &lam[i][k - 1] - &l * &t) / &d[k - 1];
                lam[i][k - 1] = (&bb * &t + &l * &lam[i][k]) / &d[k];
            }
            d[k - 1] = bb;
            k = if k > 2 { k - 1 } else { 2 };
        } else {
            for l in (1..k - 1).rev() {
                red(b, &mut lam, &d, k, l);
            }
            k += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn short_multiples_are_short() {
        let c = Curve::secp256k1();
        let mut x = BigUint::from(0x1234_5678_9abc_def0u64);
        for _ in 0..200 {
            x = (&x * &x + 7u32) % &c.n;
            let v = c.short_multiple(&x);
            for e in &v {
                assert!(e.magnitude().bits() <= 70, "{e} too long");
            }
        }
    }

    #[test]
    fn recover_matches_double_and_add() {
        let c = Curve::secp256k1();
        // 2·G + 3·G = 5·G
        let g = c.g.clone();
        let five = c.recover(&g, &BigUint::from(2u32), &BigUint::from(3u32)).unwrap();
        let five2 = c.recover(&g, &BigUint::from(5u32), &BigUint::from(0u32)).unwrap();
        assert_eq!(five, five2);
    }
}

