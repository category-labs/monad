import Proof.Avx2.Block
import Proof.Avx2.Memory

namespace Jumpdest.Avx2.Proof
open Jumpdest.Proof
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Exact pure execution of the block loop with local mutable variables, used only in the proof. -/
def scanChunks : List __m256i → Nat → __m128i → Bitmap → Bitmap × __m128i
  | [], _, entry, bits => (bits, entry)
  | op::ops, b, entry, bits =>
    let result := pair op entry
    scanChunks ops (b+1) result.2 (store (32*b) result.1 (List.range 32) bits)

theorem scanChunks_size (ops : List __m256i) (b : Nat) (entry : __m128i) (bits : Bitmap) :
    (scanChunks ops b entry bits).1.size = bits.size := by
  induction ops generalizing b entry bits with
  | nil => rfl
  | cons op ops ih => simp only [scanChunks, ih, store_size]

/-- The outer-loop invariant: processed entries agree with the decoder;
    entries outside the processed interval retain their previous values. -/
theorem scanChunks_at (ops : List __m256i) (b : Nat)
    (skip : Byte) (hskip : skip ≤ 32) (bits : Bitmap) (pc : Nat) (hp : pc < bits.size) :
    (scanChunks ops b (_mm_set1_epi8 (0x70+skip)) bits).1[pc]! =
      (if 32*b ≤ pc ∧ pc < 32*b+32*ops.length then
        ((stream (ops.flatMap pairBytes) skip).1[pc-32*b]?).getD false else bits[pc]!) := by
  induction ops generalizing b skip bits with
  | nil =>
    simp only [scanChunks, List.length_nil, Nat.mul_zero, Nat.add_zero]
    rw [if_neg (by omega)]
  | cons op ops ih =>
    simp only [scanChunks]
    rw [pair_eq_stream op skip hskip]
    rw [ih (b+1) _ (stream_carry_le _ _ hskip) _ (by simpa only [store_size] using hp)]
    rw [store_range_at _ _ _ _ hp]
    simp only [List.length_cons, List.flatMap_cons, stream_append]
    by_cases hbefore : pc < 32*b
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · by_cases hblock : pc < 32*b+32
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
        rw [streamMask_get _ _ _ (by omega)]
        rw [List.getElem?_append_left (by rw [stream_length, pairBytes_length]; omega)]
      · by_cases hafter : 32*b+32*(ops.length+1) ≤ pc
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        · rw [if_pos (by omega), if_pos (by omega)]
          rw [List.getElem?_append_right (by rw [stream_length, pairBytes_length]; omega)]
          simp only [stream_length, pairBytes_length]
          congr 2

def blockBody (code : Array Byte) (b : Nat) (state : Bitmap × __m128i) :
    Id (ForInStep (Bitmap × __m128i)) := do
  let result := pair (_mm256_loadu_si256 code (32*b)) state.2
  return .yield (store (8*(4*b)) result.1 (List.range 32) state.1, result.2)

theorem forIn_eq_scanChunks (code : Array Byte) (b n : Nat) (entry : __m128i) (bits : Bitmap) :
    forIn (List.range' b n) (bits, entry) (blockBody code) =
      scanChunks ((List.range' b n).map (fun b => _mm256_loadu_si256 code (32*b))) b entry bits := by
  induction n generalizing b entry bits with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_succ, List.forIn_cons]
    change forIn (List.range' (b+1) n)
      (store (8*(4*b)) (pair (_mm256_loadu_si256 code (32*b)) entry).1 (List.range 32) bits,
        (pair (_mm256_loadu_si256 code (32*b)) entry).2) (blockBody code) = _
    rw [ih]
    simp only [List.map_cons, scanChunks]
    congr 2 <;> omega

theorem find_eq_scanChunks (code : Array Byte) (code_size : Nat) (bits : Bitmap) :
    find_jumpdests_avx2 code code_size bits =
      (scanChunks ((List.range ((code_size+31)/32)).map
        (fun b => _mm256_loadu_si256 code (32*b))) 0 (_mm_set1_epi8 0x70) bits).1 := by
  rw [find_jumpdests_avx2_eq_pairs]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  change (forIn (List.range' 0 ((code_size+31)/32))
    (bits, _mm_set1_epi8 0x70) (blockBody code)).1 = _
  rw [forIn_eq_scanChunks, ← List.range_eq_range']

end Jumpdest.Avx2.Proof
