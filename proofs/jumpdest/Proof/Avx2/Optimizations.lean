import Avx2Intrinsics
import Std.Tactic.BVDecide

namespace Jumpdest.Avx2.Proof
set_option maxRecDepth 100000

/-- If the candidate-byte mask is empty, intersecting it with any instruction
    boundary mask has an empty movemask too. No assumption about PUSH layout
    or incoming carry is needed. -/
theorem movemask_and_guard (a b : __m256i) :
    (if _mm256_movemask_epi8 b != 0 then
      _mm256_movemask_epi8 (_mm256_and_si256 a b) else 0) =
    _mm256_movemask_epi8 (_mm256_and_si256 a b) := by
  simp only [_mm256_movemask_epi8, _mm256_and_si256, byte,
    List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Nat.reduceMul, __m256i]
  bv_decide

end Jumpdest.Avx2.Proof
