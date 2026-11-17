import Proof.Scalar
import Proof.Avx2.Correctness

/-! Public equivalence theorems for the C++-aligned scalar and AVX2 definitions. -/
namespace Jumpdest

/-- Equality of the complete output arrays, for every finite input byte array. -/
theorem simd_eq_scalar (code : Array Byte) :
    Avx2.jumpdests_avx2 code = jumpdests_scalar code := by
  apply Array.ext
  · rw [jumpdests_avx2_size, jumpdests_scalar_size]
  · intro pc hs ht
    have hp : pc < code.size := by simpa only [jumpdests_avx2_size] using hs
    have h := (simd_at_stream code pc hp).trans (Proof.scalar_at_stream code pc hp).symm
    simpa only [getElem!_pos (Avx2.jumpdests_avx2 code) pc hs,
      getElem!_pos (jumpdests_scalar code) pc ht] using h

#print axioms simd_eq_scalar
end Jumpdest
