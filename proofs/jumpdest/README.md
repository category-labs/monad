# Jumpdest equivalence

Lean 4 translations of the scalar and AVX2 jumpdest scans on
`simd-jumpdest-scan`, with a proof that they return identical Boolean bitmaps
for every input byte array.

- [Scalar.lean](Scalar.lean), [Avx2.lean](Avx2.lean): scan definitions, aligned with C++ names.
- [Avx2Intrinsics.lean](Avx2Intrinsics.lean): intrinsic value semantics and documentation links.
- [Types.lean](Types.lean): shared types, opcodes, padding, and bitmap copy.
- [Equivalence.lean](Equivalence.lean): final theorem, `simd_eq_scalar`.
- [Proof/](Proof/): supporting lemmas.

Run `lake build` from this directory to check the proofs.
The bit-vector proofs use native `bv_decide`; the build prints the theorem's axioms.
