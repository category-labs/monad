import Proof.Avx2.Scan
import Proof.Avx2.Loads

/-! Output size and pointwise decoder agreement for the actual AVX2 wrapper. -/
namespace Jumpdest
open Avx2.Proof

theorem jumpdests_avx2_size (code : Array Byte) :
    (Avx2.jumpdests_avx2 code).size = code.size := by
  unfold Avx2.jumpdests_avx2
  rw [find_eq_scanChunks, scanChunks_size]
  simp

/-- All in-range output bits of the actual intrinsic loop agree with the decoder. -/
theorem simd_at_stream (code : Array Byte) (pc : Nat) (hp : pc < code.size) :
    (Avx2.jumpdests_avx2 code)[pc]! = ((Proof.stream code.toList 0).1[pc]?).getD false := by
  unfold Avx2.jumpdests_avx2
  rw [find_eq_scanChunks]
  have hb : code.size ≤ 32*((code.size+31)/32) := by omega
  have h := scanChunks_at
    ((List.range ((code.size+31)/32)).map (fun b => Avx2._mm256_loadu_si256
      (pad code) (32*b))) 0 0 (by decide)
    (Array.replicate code.size false) pc (by simpa using hp)
  have hz : (0x70 : Byte) + 0 = 0x70 := by decide
  rw [hz] at h
  simp only [Nat.mul_zero, Nat.zero_add, Nat.sub_zero,
    List.length_map, List.length_range] at h
  rw [if_pos (by omega)] at h
  rw [h]
  have ht := Proof.stream_take
    (((List.range ((code.size+31)/32)).map (fun b => Avx2._mm256_loadu_si256
      (pad code) (32*b))).flatMap Avx2.Proof.pairBytes) 0 code.size
  rw [padded_take code _ hb] at ht
  have he := congrArg (fun xs : List Bool => (xs[pc]?).getD false) ht
  simpa only [List.getElem?_take, if_pos hp] using he

end Jumpdest
