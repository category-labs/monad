import Types
import Std.Tactic.BVDecide

/-! Proof-only byte decoder shared by the scalar and AVX2 arguments. -/
namespace Jumpdest.Proof

def immediate (op : Byte) : Byte :=
  if 0x60 ≤ op ∧ op ≤ 0x7f then op - 0x5f else 0

/-- One byte of a streaming decoder. `skip` counts outstanding PUSH data. -/
def skipNext (op skip : Byte) : Byte := if skip == 0 then immediate op else skip - 1

/-- Auxiliary byte-by-byte decoder; unlike the scalar loop this visits data bytes. -/
def stream : List Byte → Byte → List Bool × Byte
  | [], skip => ([], skip)
  | op :: rest, skip =>
      let result := stream rest (skipNext op skip)
      ((skip == 0 && op == 0x5b) :: result.1, result.2)

theorem stream_length (code : List Byte) (skip : Byte) :
    (stream code skip).1.length = code.length := by
  induction code generalizing skip with
  | nil => rfl
  | cons op rest ih => simpa only [stream, List.length_cons] using congrArg Nat.succ (ih _)

theorem stream_append (a b : List Byte) (skip : Byte) :
    stream (a ++ b) skip =
      ((stream a skip).1 ++ (stream b (stream a skip).2).1,
       (stream b (stream a skip).2).2) := by
  induction a generalizing skip with
  | nil => rfl
  | cons op rest ih => simp only [List.cons_append, stream, ih, List.cons_append]

theorem stream_take (code : List Byte) (skip : Byte) (n : Nat) :
    (stream code skip).1.take n = (stream (code.take n) skip).1 := by
  induction code generalizing skip n with
  | nil => simp [stream]
  | cons op rest ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [stream, List.take_succ_cons] using
        congrArg (List.cons (skip == 0 && op == 0x5b)) (ih _ _)

theorem skipNext_succ (op : Byte) (k : Nat) (hk : k+1 < 256) :
    skipNext op (BitVec.ofNat 8 (k+1)) = BitVec.ofNat 8 k := by
  have hz : (BitVec.ofNat 8 (k+1) == (0 : Byte)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hv := congrArg BitVec.toNat (beq_iff_eq.mp h)
    change (k+1) % 256 = 0 at hv
    omega
  simp only [skipNext, hz, Bool.false_eq_true, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  change (255 + (k+1) % 256) % 256 = k % 256
  omega

theorem stream_skip (code : List Byte) (k : Nat) (hk : k < 256) :
    (stream code (BitVec.ofNat 8 k)).1 =
      List.replicate (min k code.length) false ++ (stream (code.drop k) 0).1 := by
  induction k generalizing code with
  | zero => simp
  | succ k ih =>
    cases code with
    | nil => simp [stream]
    | cons op rest =>
      have hz : (BitVec.ofNat 8 (k+1) == (0 : Byte)) = false := by
        apply Bool.eq_false_iff.mpr
        intro h
        have hv := congrArg BitVec.toNat (beq_iff_eq.mp h)
        change (k+1) % 256 = 0 at hv
        omega
      simp only [stream, hz, Bool.false_and, skipNext_succ op k hk,
        List.length_cons, List.drop_succ_cons]
      rw [ih rest (by omega)]
      have hm : min (k+1) (rest.length+1) = min k rest.length + 1 := by omega
      rw [hm, List.replicate_succ, List.cons_append]

/-- The stream carry is always at most PUSH32's immediate length. -/
theorem skipNext_le (op skip : Byte) (h : skip ≤ 32) : skipNext op skip ≤ 32 := by
  simp only [skipNext, immediate, Byte] at *
  bv_decide

theorem stream_carry_le (code : List Byte) (skip : Byte) (h : skip ≤ 32) :
    (stream code skip).2 ≤ 32 := by
  induction code generalizing skip with
  | nil => exact h
  | cons op rest ih => exact ih _ (skipNext_le op skip h)

end Jumpdest.Proof
