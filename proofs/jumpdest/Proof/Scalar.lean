import Scalar
import Proof.Stream
import Init.Internal.Order.While

/-! Invariants for the C++-aligned scalar loop with a local mutable bitmap. -/
namespace Jumpdest
namespace Proof
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- C++ PUSH0..PUSH32 classification agrees with the decoder's skip count. -/
theorem push_index_eq_immediate (op : Byte) :
    (if is_push_opcode op then get_push_opcode_index op else 0) = (immediate op).toNat := by
  unfold is_push_opcode get_push_opcode_index immediate EvmOpCode.PUSH0 EvmOpCode.PUSH32
  simp only [decide_eq_true_eq]
  split
  next h =>
    change 95 ≤ op.toNat ∧ op.toNat ≤ 127 at h
    split
    next hi =>
      change op.toNat - 95 = (161 + op.toNat) % 256
      omega
    next hi =>
      change ¬(96 ≤ op.toNat ∧ op.toNat ≤ 127) at hi
      change op.toNat - 95 = 0
      omega
  next h =>
    split
    next hi =>
      change 96 ≤ op.toNat ∧ op.toNat ≤ 127 at hi
      change ¬(95 ≤ op.toNat ∧ op.toNat ≤ 127) at h
      omega
    next => rfl

/-- Proof-only description of the marks remaining at or after absolute index i. -/
def remaining (code : List Byte) (i pc : Nat) : Bool :=
  if i ≤ pc then ((stream (code.drop i) 0).1[pc-i]?).getD false else false

theorem remaining_before (code : List Byte) (i pc : Nat) (h : pc < i) :
    remaining code i pc = false := by
  simp [remaining, Nat.not_le.mpr h]

theorem stream_instruction (code : List Byte) (i : Nat) (h : i < code.length) :
    (stream (code.drop i) 0).1 =
      (code[i] == 0x5b) ::
        (List.replicate (min (immediate code[i]).toNat (code.length-(i+1))) false ++
          (stream (code.drop (i+1+(immediate code[i]).toNat)) 0).1) := by
  rw [List.drop_eq_getElem_cons h]
  simp only [stream, skipNext, beq_self_eq_true, ↓reduceIte, Bool.true_and]
  have hs := stream_skip (code.drop (i+1)) (immediate code[i]).toNat (immediate code[i]).isLt
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hs
  rw [hs]
  simp only [List.length_drop, List.drop_drop]

theorem remaining_step (code : List Byte) (i pc : Nat)
    (hi : i < code.length) (hp : pc < code.length) :
    remaining code i pc = (((i == pc) && (code[i] == 0x5b)) ||
      remaining code (i+1+(immediate code[i]).toNat) pc) := by
  by_cases hbefore : pc < i
  · have hn : (i == pc) = false := by simp; omega
    rw [remaining_before code i pc hbefore, hn,
      remaining_before code _ pc (by omega)]
    rfl
  · have hip : i ≤ pc := by omega
    by_cases heq : pc = i
    · subst pc
      rw [remaining_before code (i+1+(immediate code[i]).toNat) i (by omega)]
      simp only [remaining, Nat.le_refl, ↓reduceIte, Nat.sub_self, stream_instruction code i hi,
        List.getElem?_cons_zero, Option.getD_some, beq_self_eq_true, Bool.true_and,
        Bool.or_false]
    · have hn : (i == pc) = false := by simp; omega
      rw [hn, Bool.false_and, Bool.false_or]
      unfold remaining
      rw [if_pos hip, stream_instruction code i hi]
      have hindex : pc-i = (pc-(i+1))+1 := by omega
      rw [hindex, List.getElem?_cons_succ]
      by_cases hnext : pc < i+1+(immediate code[i]).toNat
      · rw [if_neg (by omega)]
        have hsmall : pc-(i+1) < min (immediate code[i]).toNat (code.length-(i+1)) := by omega
        rw [List.getElem?_append_left (by simpa only [List.length_replicate] using hsmall),
          List.getElem?_replicate_of_lt hsmall]
        rfl
      · rw [if_pos (by omega)]
        have hmin : min (immediate code[i]).toNat (code.length-(i+1)) =
            (immediate code[i]).toNat := by omega
        rw [hmin, List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
        simp only [List.length_replicate]
        congr 2
        omega

/-- The actual while loop, generalized to an arbitrary starting index for induction. -/
def loop (code : Array Byte) (code_size i : Nat) (bits : Bitmap) : Bitmap := Id.run do
  let mut bits := bits
  let mut i := i
  while i < code_size do
    let op := code.getD i 0
    if op == EvmOpCode.JUMPDEST then
      bits := bits.set! i true
    if is_push_opcode op then
      i := i + get_push_opcode_index op
    i := i + 1
  return bits

theorem find_eq_loop (code : Array Byte) (code_size : Nat) (bits : Bitmap) :
    find_jumpdests_scalar code code_size bits = loop code code_size 0 bits := rfl

/-- One iteration of the while loop, using Lean's standard unfolding theorem. -/
theorem loop_eq (code : Array Byte) (code_size i : Nat) (bits : Bitmap) :
    loop code code_size i bits =
      if i < code_size then
        let op := code.getD i 0
        loop code code_size
          ((if is_push_opcode op then i + get_push_opcode_index op else i) + 1)
          (if op == EvmOpCode.JUMPDEST then bits.set! i true else bits)
      else bits := by
  conv => lhs; unfold loop
  simp only [ForIn.forIn]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  by_cases hi : i < code_size
  · by_cases hj : (code.getD i 0 == EvmOpCode.JUMPDEST) = true <;>
      by_cases hp : is_push_opcode (code.getD i 0) = true <;>
      simp only [hi, hj, hp, ↓reduceIte] <;> rfl
  · simp only [hi, ↓reduceIte]
    rfl

theorem loop_step (code : Array Byte) (i : Nat) (bits : Bitmap) (h : i < code.size) :
    loop code code.size i bits =
      loop code code.size (i+1+(immediate code[i]).toNat)
        (if code[i] == 0x5b then bits.set! i true else bits) := by
  rw [loop_eq]
  simp only [h, ↓reduceIte, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]
  have ha : (if is_push_opcode code[i] then i + get_push_opcode_index code[i] else i) + 1 =
      i + 1 + (immediate code[i]).toNat := by
    rw [← push_index_eq_immediate]
    split <;> omega
  simp only [ha, EvmOpCode.JUMPDEST]
  rfl

theorem loop_stop (code : Array Byte) (i : Nat) (bits : Bitmap) (h : code.size ≤ i) :
    loop code code.size i bits = bits := by
  rw [loop_eq]
  simp only [Nat.not_lt.mpr h, ↓reduceIte]

theorem loop_size (code : Array Byte) (i : Nat) (bits : Bitmap) :
    (loop code code.size i bits).size = bits.size := by
  by_cases h : i < code.size
  · rw [loop_step code i bits h, loop_size]
    split <;> simp
  · rw [loop_stop code i bits (by omega)]
termination_by code.size - i
decreasing_by omega

theorem update_at (bits : Bitmap) (i pc : Nat) (op : Byte) (hi : i < bits.size) :
    (if op == 0x5b then bits.set! i true else bits)[pc]! =
      (bits[pc]! || ((i == pc) && (op == 0x5b))) := by
  by_cases hop : op == 0x5b
  · simp only [hop, ↓reduceIte, Bool.and_true]
    by_cases heq : i = pc
    · subst pc
      rw [Array.getElem!_set!_self bits i true hi]
      simp
    · rw [Array.getElem!_set!_ne bits i pc true heq]
      simp [heq]
  · have hf : (op == 0x5b) = false := Bool.eq_false_iff.mpr hop
    simp only [hf, Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.or_false]

/-- For arbitrary initial bitmap contents, the loop preserves old true bits
    and adds exactly the remaining instruction-start JUMPDESTs. -/
theorem loop_at (code : Array Byte) (i pc : Nat) (bits : Bitmap)
    (hs : bits.size = code.size) (hp : pc < code.size) :
    (loop code code.size i bits)[pc]! =
      (bits[pc]! || remaining code.toList i pc) := by
  by_cases hi : i < code.size
  · rw [loop_step code i bits hi]
    have hu : (if code[i] == 0x5b then bits.set! i true else bits).size = code.size := by
      split <;> simp [hs]
    rw [loop_at code (i+1+(immediate code[i]).toNat) pc _ hu hp]
    rw [update_at bits i pc code[i] (by omega)]
    have hr := remaining_step code.toList i pc (by simpa using hi) (by simpa using hp)
    simp only [Array.getElem_toList] at hr
    rw [hr, Bool.or_assoc]
  · rw [loop_stop code i bits (by omega), remaining_before code.toList i pc (by omega)]
    simp
termination_by code.size - i
decreasing_by omega

/-- Appended storage does not affect the scalar loop when its bound stays
    at the original code size. This holds for any suffix and initial bitmap. -/
theorem loop_append (code suffix : Array Byte) (i : Nat) (bits : Bitmap) :
    loop (code ++ suffix) code.size i bits =
      loop code code.size i bits := by
  conv => lhs; rw [loop_eq]
  conv => rhs; rw [loop_eq]
  by_cases hi : i < code.size
  · have hread : (code ++ suffix).getD i 0 = code.getD i 0 := by
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hi]
    simp only [hi, ↓reduceIte, hread, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hi, Option.getD_some]
    split <;> rw [loop_append]
  · simp only [hi, ↓reduceIte]
termination_by code.size - i
decreasing_by all_goals omega

theorem scalar_at_stream (code : Array Byte) (pc : Nat) (hp : pc < code.size) :
    (jumpdests_scalar code)[pc]! = ((stream code.toList 0).1[pc]?).getD false := by
  have h := loop_at code 0 pc (Array.replicate code.size false) (by simp) hp
  have hz : (Array.replicate code.size false)[pc]! = false := by
    rw [getElem!_pos _ _ (by simpa using hp)]
    simp
  simpa only [jumpdests_scalar, find_eq_loop, pad, loop_append, remaining, Nat.zero_le, ↓reduceIte, List.drop_zero,
    Nat.sub_zero, hz, Bool.false_or] using h

end Proof

theorem jumpdests_scalar_size (code : Array Byte) :
    (jumpdests_scalar code).size = code.size := by
  simp only [jumpdests_scalar, Proof.find_eq_loop, pad, Proof.loop_append]
  rw [Proof.loop_size]
  simp

end Jumpdest
