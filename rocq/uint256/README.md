# uint256 Formal Verification

This project contains formal specifications and proofs for the uint256 implementation in `category/core/runtime/uint256.hpp`.

## Goal

Prove that the low-level C++ implementation of 256-bit unsigned integer operations correctly implements the mathematical specifications defined as operations modulo 2^256.

## Project Structure

```
uint256-verification/
├── theories/
│   ├── Spec.v          # High-level specifications (Z/(2^256)Z)
│   ├── Primitives.v    # 64-bit primitive operations
│   ├── Arithmetic.v    # 256-bit arithmetic operations (TODO)
│   ├── Division.v      # Division algorithm verification (TODO)
│   ├── Modular.v       # addmod, mulmod verification (TODO)
│   └── Special.v       # byte, signextend, exp, etc. (TODO)
├── tests/
│   └── TestVectors.v   # QuickChick property-based tests (TODO)
├── extraction/
│   └── Extract.v       # OCaml code extraction (TODO)
└── _CoqProject         # Coq project configuration
```

## Building

### Prerequisites

Install Rocq/Coq and required libraries:

```bash
opam install coq
# Optional but recommended for future phases:
# opam install coq-fiat-crypto coq-compcert coq-bbv
```

### Build Instructions

```bash
cd uint256-verification
coq_makefile -f _CoqProject -o Makefile
make
```

## Current Status

### Phase 1: Foundation Setup ✓

- [x] `Spec.v`: High-level mathematical specifications
  - Type definitions (uint256 as {z : Z | 0 ≤ z < 2^256})
  - Specifications for all major operations
  - Basic lemmas (commutativity, associativity)

- [x] `Primitives.v`: 64-bit primitive operations
  - addc/subb with carry/borrow
  - mulx (64×64→128)
  - div (128÷64→64)
  - shld/shrd double-precision shifts
  - Correctness lemmas for primitives

### TODO (Future Phases)

- [ ] Phase 2: Prove primitive operation correctness
- [ ] Phase 3: Implement and prove 256-bit arithmetic
- [ ] Phase 4: Prove division algorithm (Knuth Algorithm D)
- [ ] Phase 5: Prove modular operations with Fiat Cryptography
- [ ] Phase 6: Prove special operations (exp, byte, signextend)
- [ ] Phase 7: Integration and validation

## Key Verification Strategy

1. **High-level specs**: Define mathematical behavior over Z with mod 2^256
2. **Mid-level implementation**: Model multi-word representation (4×uint64)
3. **Low-level correspondence**: Relate to actual C++ implementation

### Proof Architecture

```
Mathematical Specification (Z/(2^256)Z)
    ↕ equivalence proofs
Multi-word Coq Implementation
    ↕ correspondence proofs
C++ uint256.hpp Implementation
```

## Key Operations Covered

### Arithmetic
- Addition, subtraction, multiplication (with/without carry)
- Division, modulo (Knuth algorithm)
- Negation
- Modular arithmetic (addmod, mulmod)

### Bitwise & Shifts
- AND, OR, XOR, NOT
- Left shift, logical right shift, arithmetic right shift
- Double-precision shifts (shld, shrd)

### Comparisons
- Unsigned: <, ≤, >, ≥, ==
- Signed: slt (signed less than)

### Special Operations
- exp (exponentiation)
- byte (extract byte at index)
- signextend (sign extension from byte position)
- byteswap (endianness conversion)
- Bit manipulation (countl_zero, countr_zero, popcount)

## References

- Source implementation: `category/core/runtime/uint256.hpp`
- Analysis report: `~/projects/claude-analysis/uint256-rocq-verification.org`

## License

Copyright (C) 2025 Category Labs, Inc.
Licensed under the GNU General Public License version 3.
