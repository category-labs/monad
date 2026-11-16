import Proof.Avx2.Circuit
import Proof.Avx2.NoPush

namespace Jumpdest.Avx2.Proof
open Jumpdest.Proof
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- The literal AVX2 loop body agrees with 32 steps of the streaming decoder. -/
theorem pair_eq_stream (op : __m256i) (skip : Byte) (hskip : skip ≤ 32) :
    pair op (_mm_set1_epi8 (0x70+skip)) =
      (streamMask op skip, _mm_set1_epi8 (0x70+(stream (pairBytes op) skip).2)) := by
  unfold pair
  split
  · rename_i h_no_push
    unfold pairFast
    apply no_push_circuit <;> first | exact hskip | exact h_no_push | rfl
  · unfold pairSlow
    apply pair_circuit <;> first | exact hskip | rfl

/-- Read one bit from a mask packed from exactly 32 Boolean values. -/
theorem mask_get (xs : List Bool) (hx : xs.length = 32) (i : Nat) (hi : i < 32) :
    (xs.zipIdx.foldl (fun mask (b,j) =>
      mask ||| ((BitVec.ofBool b).zeroExtend 32 <<< j)) (0 : BitVec 32)).getLsbD i =
      (xs[i]?).getD false := by
  let f : Fin 32 → Bool := fun j => xs[j.val]'(by omega)
  have he : xs = List.ofFn f := by
    apply List.ext_getElem
    · simp [hx]
    · intro j hj hj'
      rw [List.getElem_ofFn]
  rw [he]
  have cases : i ∈ List.range 32 := List.mem_range.mpr hi
  change i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] at cases
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [List.ofFn_succ, List.ofFn_zero,
      List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    bv_decide

theorem streamMask_get (op : __m256i) (skip : Byte) (i : Nat) (hi : i < 32) :
    (streamMask op skip).getLsbD i = ((stream (pairBytes op) skip).1[i]?).getD false := by
  exact mask_get _ (by rw [stream_length, pairBytes_length]) i hi

end Jumpdest.Avx2.Proof
