import Avx2Intrinsics
import Init.Data.Range.Lemmas

namespace Jumpdest.Avx2.Proof
set_option maxHeartbeats 2000000

def store (start : Nat) (mask : BitVec 32) (is : List Nat) (bits : Bitmap) : Bitmap :=
  is.foldl (fun bits i => bits.setIfInBounds (start+i) (mask.getLsbD i)) bits

/-- The bitmap's four-byte copy is exactly the store fold. -/
theorem store_u32_le_eq_store (bits : Bitmap) (offset : Nat) (mask : BitVec 32) :
    bits.store_u32_le offset mask = store (8*offset) mask (List.range 32) bits := rfl

theorem store_size (start : Nat) (mask : BitVec 32) (is : List Nat) (bits : Bitmap) :
    (store start mask is bits).size = bits.size := by
  induction is generalizing bits with
  | nil => rfl
  | cons i is ih =>
    change (store start mask is (bits.setIfInBounds (start+i) (mask.getLsbD i))).size = _
    rw [ih, Array.size_setIfInBounds]

theorem store_at (start : Nat) (mask : BitVec 32) (is : List Nat) (bits : Bitmap)
    (pc : Nat) (hp : pc < bits.size) :
    (store start mask is bits)[pc]! =
      (if ∃ i ∈ is, start+i = pc then mask.getLsbD (pc-start) else bits[pc]!) := by
  induction is generalizing bits with
  | nil => simp [store]
  | cons i is ih =>
    change (store start mask is (bits.setIfInBounds (start+i) (mask.getLsbD i)))[pc]! = _
    rw [ih _ (by simpa using hp)]
    by_cases h : ∃ j ∈ is, start+j = pc
    · simp only [h, ↓reduceIte]
      rw [if_pos (by obtain ⟨j, hj, he⟩ := h; exact ⟨j, List.mem_cons_of_mem i hj, he⟩)]
    · simp only [h, ↓reduceIte]
      by_cases he : start+i = pc
      · subst pc
        have hi : start+i-start = i := by omega
        rw [if_pos (by exact ⟨i, List.mem_cons_self, rfl⟩), hi]
        simp only [← Array.set!_eq_setIfInBounds]
        exact Array.getElem!_set!_self bits (start+i) (mask.getLsbD i) hp
      · have hn : ¬ ∃ j ∈ i::is, start+j = pc := by
          rintro ⟨j, hj, heq⟩
          rcases List.mem_cons.mp hj with rfl | hj
          · exact he heq
          · exact h ⟨j, hj, heq⟩
        rw [if_neg hn]
        simp only [← Array.set!_eq_setIfInBounds]
        exact Array.getElem!_set!_ne bits (start+i) pc (mask.getLsbD i) he

theorem store_range_at (start : Nat) (mask : BitVec 32) (bits : Bitmap)
    (pc : Nat) (hp : pc < bits.size) :
    (store start mask (List.range 32) bits)[pc]! =
      (if start ≤ pc ∧ pc < start+32 then mask.getLsbD (pc-start) else bits[pc]!) := by
  rw [store_at _ _ _ _ _ hp]
  have he : (∃ i ∈ List.range 32, start+i = pc) ↔ (start ≤ pc ∧ pc < start+32) := by
    constructor
    · rintro ⟨i, hi, rfl⟩
      have := List.mem_range.mp hi
      omega
    · intro h
      exact ⟨pc-start, List.mem_range.mpr (by omega), by omega⟩
  simp only [he]

end Jumpdest.Avx2.Proof
