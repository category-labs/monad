import Init

namespace Jumpdest
abbrev Byte := BitVec 8
abbrev Bitmap := Array Bool

/-- Copy a 32-bit source (four bytes) at a byte offset, in x86 little-endian
    order. The logical bitmap omits C++ allocation-padding bits, so writes
    beyond its size are discarded. This truncation models the representation;
    it is not a bounds check performed by C++'s std::memcpy. -/
def Bitmap.store_u32_le (bits : Bitmap) (offset : Nat) (src : BitVec 32) : Bitmap :=
  (List.range 32).foldl
    (fun bits i => bits.setIfInBounds (8 * offset + i) (src.getLsbD i)) bits

namespace EvmOpCode
def JUMPDEST : Byte := 0x5b
def PUSH0 : Byte := 0x5f
def PUSH32 : Byte := 0x7f
end EvmOpCode

/-- C++ Intercode::pad, viewed from its returned code pointer: append 32 bytes
    for a truncated PUSH32 and one STOP byte. The preceding 30-byte allocation
    padding is unused by these forward scans and is not represented here. -/
def pad (code : Array Byte) : Array Byte :=
  code ++ Array.replicate (32 + 1) 0

end Jumpdest
