import Types

namespace Jumpdest

/-- C++ includes PUSH0, whose immediate length is zero. -/
def is_push_opcode (opcode : Byte) : Bool :=
  decide (EvmOpCode.PUSH0 ≤ opcode ∧ opcode ≤ EvmOpCode.PUSH32)

/-- Used only after is_push_opcode, as in the C++ function. -/
def get_push_opcode_index (opcode : Byte) : Nat := opcode.toNat - EvmOpCode.PUSH0.toNat

/-- Return the updated bitmap. `code_size` is the original length;
    the caller supplies at least that many code bytes and bitmap entries. -/
def find_jumpdests_scalar (code : Array Byte) (code_size : Nat) (bits : Bitmap) : Bitmap := Id.run do
  let mut bits := bits
  let mut i := 0
  while i < code_size do
    let op := code.getD i 0
    if op == EvmOpCode.JUMPDEST then
      bits := bits.set! i true
    if is_push_opcode op then
      i := i + get_push_opcode_index op
    i := i + 1
  return bits

def jumpdests_scalar (code : Array Byte) : Bitmap :=
  let padded_code := pad code
  let bits := Array.replicate code.size false
  find_jumpdests_scalar padded_code code.size bits

end Jumpdest
