import Proof.Avx2.Body

/-! Byte packing, loads, and preservation of the unpadded input prefix. -/
namespace Jumpdest.Avx2.Proof
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Packing bytes and reading a lane are inverse operations. -/
theorem byte_bytes256 (f : Nat → Byte) (i : Nat) (hi : i < 32) :
    byte (bytes 256 f) i = f i := by
  have cases : i ∈ List.range 32 := List.mem_range.mpr hi
  change i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31] at cases
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [byte, bytes, Nat.reduceDiv, List.range_succ, List.range_zero, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Byte]
    bv_decide

theorem pairBytes_load (code : Array Byte) (offset : Nat) :
    pairBytes (_mm256_loadu_si256 code offset) =
      (List.range 32).map (fun i => code.getD (offset+i) 0) := by
  unfold pairBytes
  have h : (fun i : Fin 32 => byte (_mm256_loadu_si256 code offset) i.val) =
      (fun i : Fin 32 => code.getD (offset+i.val) 0) := by
    funext i
    exact byte_bytes256 (fun j => code.getD (offset+j) 0) i.val i.isLt
  rw [h]
  rfl

theorem loaded_flat (code : Array Byte) (n : Nat) :
    ((List.range n).map (fun b => _mm256_loadu_si256 code (32*b))).flatMap pairBytes =
      (List.range (32*n)).map (fun i => code.getD i 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, pairBytes_load, Nat.mul_succ, List.range_add, List.map_append,
      List.map_map, Function.comp_def]

theorem padded_take (code : Array Byte) (n : Nat) (hn : code.size ≤ 32*n) :
    (((List.range n).map (fun b => _mm256_loadu_si256
      (pad code) (32*b))).flatMap pairBytes).take code.size = code.toList := by
  rw [loaded_flat]
  apply List.ext_getElem
  · simp only [List.length_take, List.length_map, List.length_range, Array.length_toList]
    omega
  · intro i hi hj
    have hic : i < code.size := by simpa only [Array.length_toList] using hj
    simp only [pad, List.getElem_take, List.getElem_map, List.getElem_range, Array.getD_eq_getD_getElem?]
    rw [Array.getElem?_append_left hic, Array.getElem?_eq_getElem hic]
    rfl

end Jumpdest.Avx2.Proof
