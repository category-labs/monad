---
title: Integer Tensor Graph Evaluation
description: Add a precompile that evaluates graphs of integer tensor operations stored as contract code
author: Category Labs (@category-labs)
discussions-to: TBD
status: Draft
type: Standards Track
category: Core
created: 2026-11-23
---

## Abstract

Add a precompile at address `0x1002` that evaluates a graph of integer
tensor operations. A graph is stored as the code of an ordinary
account, in a compact binary format. Graphs support a fixed set of
tensor operations on signed and unsigned integer types of at most 64
bits, with no support for control flow, side-effects, floating point
or dynamic shapes. Callers pass the graph's inputs by value, by
reference to another account's code or by reference to the caller's
storage, and receive the outputs back or have them written to the
caller's storage.

## Motivation

Numeric work in EVM code is expensive. Every value is a 256-bit word,
so a 32-bit multiplication with wrapping takes a multiplication and a
sign extension, and a 16.16 fixed-point multiplication takes eight
opcodes and 30 gas. Loops over arrays pay for bounds checks, loop
control and memory or storage accesses on every element. Workloads
that run the same arithmetic over many values, or long chains of
narrow integer arithmetic, such as inference with quantized neural
networks, order matching, pricing curves and simulations, cost far
more in gas than the work they do.

A precompile that takes a whole computation as one graph of tensor
operations can execute it with machine-width integer arithmetic,
without per-element dispatch. Because the graph is fixed in advance,
its validity, memory use and most of its cost are known before it
runs, which opens the door to efficient compilation.

## Specification

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.ietf.org/rfc/rfc2119.html) and [RFC 8174](https://www.ietf.org/rfc/rfc8174.html).

### Parameters

| Name                       | Value                        |
|----------------------------|------------------------------|
| `GRAPH_EVAL_ADDRESS`       | `0x1002`                     |
| `GRAPH_MAGIC`              | `0x7ffe` (the bytes `fe 7f`) |
| `GRAPH_VERSION`            | `0`                          |
| `MAX_GRAPH_INPUTS`         | `8`                          |
| `MAX_GRAPH_OUTPUTS`        | `8`                          |
| `MAX_GRAPH_OPS`            | `16 * 1024`                  |
| `MAX_RANK`                 | `8`                          |
| `MAX_DIM`                  | `65535`                      |
| `MAX_SCALAR_INPUTS`        | `8`                          |
| `MAX_SCALAR_REGISTERS`     | `14`                         |
| `MAX_SCALAR_FNS`           | `255`                        |
| `MAX_FRACTIONAL_BITS`      | `63`                         |
| `ARENA_SIZE`               | 64 MiB                       |
| `ARENA_ALIGNMENT`          | `64`                         |
| `MAX_CALL_TENSORS`         | `16`                         |
| `SELECTOR_EVAL_GRAPH`      | `0xd259ffd8`                 |
| `SELECTOR_EVAL_GRAPH_INTO` | `0x2a054e80`                 |

### Types and shapes

All tensors have a tensor type which is an element type (or dtype) and
a shape. Valid dtypes are those in the list below. Any id not in it is
invalid.

| id | dtype    | Byte size |
|----|----------|-----------|
| 0  | `uint8`  | 1         |
| 1  | `uint16` | 2         |
| 2  | `uint32` | 4         |
| 3  | `uint64` | 8         |
| 4  | `int8`   | 1         |
| 5  | `int16`  | 2         |
| 6  | `int32`  | 4         |
| 7  | `int64`  | 8         |

A shape is a list of dimensions of length between 0 and `MAX_RANK`.
Each dimension is a number between 0 and `MAX_DIM`. The element count
of a shape is the product of each of its dimensions. The byte size of
a tensor type is the product of the element count of its shape times
the byte size of its dtype.

### Graph and tensor storage

A graph is stored as the code of an account. To distinguish it from
EVM bytecode, graph-representing code (henceforth graphcode) must
start with the byte sequence `GRAPH_MAGIC` (`fe 7f`). The first byte
corresponds to the `INVALID` opcode, so that a call that executes the
account as EVM code will fail at once.

Graphs are deployed as ordinary contract code, with `CREATE` or
`CREATE2`, subject to the usual code size limit.

Tensors can also be stored as the code of an account and used directly
in graphcode as `TensorRef` nodes (see Ops) or passed as arguments to
`graphEval` invocations **CLAUDE: reference the section for this**.
Tensors living in contract code are represented as literal tensors
(see `Literal` in section Ops) and can be stored at any offset.
**CLAUDE: try to add Markdown links when we reference a section**

**CLAUDE: we're getting rid of the "first byte is 00" condition. This
is so that someone may be able to e.g. deploy a tensor as a Literal node and
have someone else read it as a TensorRef, and I don't really see a reason to keep it**
Its code is a `0x00` byte (`STOP`, so a call that executes it stops at
once), then any number of tensors, each encoded as a `Literal` node's
parameters (see Ops). A reference to a tensor is the account's address
and the byte offset of the tensor's encoding in its code, counted from
the code's first byte.

### Graph encoding

**CLAUDE: are you sure this is how RFC keywords are used? In this section we don't
use them to constrain the implementation, but inputs to it, which is maybe odd. Perhaps
we should say something like "an implementation MUST reject a graph that doesn't follow
blah blah"**

All integers are little-endian. A graph's code MUST follow the structure below:

```
graph :=
    magic: u16                    GRAPH_MAGIC
    version: u8                   GRAPH_VERSION
    n_inputs: u8                  at most MAX_GRAPH_INPUTS
    inputs: type[n_inputs]
    n_outputs: u8                 at most MAX_GRAPH_OUTPUTS
    outputs: u16[node_id]
    n_ops: u16                    at most MAX_GRAPH_OPS
    ops: op[n_ops]

type :=
    dtype: u8
    shape: shape

shape :=
    rank: u8                      at most MAX_RANK
    dims: u16[rank]

node_id := u16

op :=
    opcode: u8
    params: params(opcode)
    inputs: node_id[arity(opcode)]    node ids
```

At a high level, a graph is a topologically-ordered sequence of nodes,
with each node consisting of an opcode, a list of parameters
(statically-determined inputs to the node, such as the dimension for a
reduction operation) and a list of inputs (given as a list of ids that
reference previous nodes).


Nodes are 0-indexed, starting with the graph's inputs followed by its
ops in order. An op's inputs MUST be the ids of earlier nodes, and
every output in the list `outputs` MUST be the id of a node. An output
MAY be a graph input, and a single node MAY appear as multiple
outputs. A valid graph MUST NOT have any trailing bytes.

### Ops

| id | op          | params                                   | inputs              |
|----|-------------|------------------------------------------|---------------------|
| 0  | `Scalar`    | see Scalar nodes                         | see Scalar nodes    |
| 1  | `Literal`   | `type`, then its elements                | 0                   |
| 2  | `TensorRef` | `type`, `address: u8[20]`, `offset: u32` | 0                   |
| 3  | `Reshape`   | `shape`                                  | 1                   |
| 4  | `Concat`    | `axis: u8`                               | 2                   |
| 5  | `MatMul`    | none                                     | 2                   |
| 6  | `QMatMul`   | `frac_bits: u8`, `dtype: u8`             | 2                   |
| 7  | `CumSum`    | `axis: u8`                               | 1                   |
| 8  | `ArgMin`    | none                                     | 1                   |
| 9  | `ArgMax`    | none                                     | 1                   |
| 10 | `ReduceSum` | `axis: u8`                               | 1                   |
| 11 | `ReduceMax` | `axis: u8`                               | 1                   |
| 12 | `Gather`    | `axis: u8`                               | 2 (values, indices) |

Validation rules and results, with `x` and `y` the inputs:

- `Literal`: its elements follow the type, little-endian, and the result is
  that tensor.
- `TensorRef`: the result has the given type. Its elements are read when the
  graph is evaluated, from the tensor at `offset` in the code of `address`,
  little-endian. Evaluation fails if that code doesn't start with `0x00`, if
  `offset` is 0, if the tensor's encoded type differs from the given type, or
  if its elements extend past the end of the code.
- `Reshape`: `x` and `shape` MUST have the same element count. The result has
  `x`'s dtype and elements, in the same row-major order, and the given shape.
- `Concat`: `x` and `y` MUST have the same dtype and rank, `axis` MUST be less
  than the rank, and the dimensions other than `axis` MUST be equal. The
  result joins them along `axis`; its dimension there, the sum of theirs, MUST
  be at most 65535.
- `MatMul`: `x` and `y` MUST be `int8` matrices (rank 2), `[m, k]` and
  `[k, n]`. The result is the `int32` matrix `[m, n]` of their exact product.
- `QMatMul`: `x` and `y` MUST be matrices of the same dtype, `[m, k]` and
  `[k, n]`. `frac_bits` MUST be at least 1 and at most the bit width of
  `dtype` and `MAX_FRACTIONAL_BITS`. Each element of the `[m, n]` result is
  the sum of its `k` products, computed modulo 2^128 (as a signed 128-bit
  value for signed dtypes, unsigned otherwise), shifted right by `frac_bits`
  rounding toward negative infinity, then wrapped to `dtype`.
- `CumSum`: `axis` MUST be less than `x`'s rank. The result has `x`'s type;
  each element is the sum of `x`'s elements up to and including its position
  along `axis`, wrapping to the dtype.
- `ArgMin` and `ArgMax`: `x` MUST have at least one element. The result is a
  rank-0 tensor of `x`'s dtype: the row-major index of the first smallest
  (largest) element, wrapped to that dtype.
- `ReduceSum` and `ReduceMax`: `axis` MUST be less than `x`'s rank, and `x`'s
  dimension along it MUST be at least 1. The result has `x`'s dtype and shape,
  with dimension 1 along `axis`, and holds the sum (wrapping) or the largest
  element along `axis`.
- `Gather`: `axis` MUST be less than the rank of `x`, and
  `rank(x) - 1 + rank(indices)` MUST be at most `MAX_RANK`. `indices` MAY have
  any dtype. The result's shape is `x`'s dimensions before `axis`, then
  `indices`' dimensions, then `x`'s dimensions after `axis`; each of its
  elements is the element of `x` with `axis` coordinate given by the
  corresponding index. Evaluation fails if any index is negative or at least
  `x`'s dimension along `axis`.

### Scalar nodes

A `Scalar` node computes every element of its output with the same short
program, over a register file of `MAX_SCALAR_REGISTERS` registers:

```
scalar :=
    output_shape: shape
    n_inputs: u8                       at most MAX_SCALAR_INPUTS
    inputs: u16[n_inputs]              node ids: registers 0 .. n_inputs - 1
    n_constants: u8
    constants: constant[n_constants]   registers n_inputs .. n_inputs + n_constants - 1
    n_fns: u8                          1 to MAX_SCALAR_FNS
    fns: fn[n_fns]

constant :=
    dtype: u8
    value: the dtype's size in bytes, little-endian

fn :=
    fn_id: u8
    params: params(fn_id)
    operands: u8[arity(fn_id)]         register numbers
    destination: u8                    omitted for the last fn
```

Validation:

- `n_inputs + n_constants` MUST be at most `MAX_SCALAR_REGISTERS`.
- Each input MUST broadcast to `output_shape`: its rank MUST be at most the
  output's, and, matching axes from the last, each of its dimensions MUST be
  1 or equal to the output's.
- Every operand MUST be a register number below `MAX_SCALAR_REGISTERS` that
  holds a value at that point: an input, a constant, or the destination of an
  earlier fn.
- Every destination MUST be at least `n_inputs + n_constants` and below
  `MAX_SCALAR_REGISTERS`. Input and constant registers are never written.
- Each register has the dtype of the value it holds. A fn's operands MUST
  have the dtypes the fn table requires, and its destination takes on the
  fn's result dtype.

The node's result has shape `output_shape` and the dtype of the last fn's
result. For each element of the output, independently: the input registers
hold the corresponding elements of the inputs, broadcast as above; the
constant registers hold the constants; the fns run in order, each reading its
operands and then writing its result to its destination; and the last fn's
result is the output element. A destination MAY be one of the fn's own
operands.

Scalar functions, with `a` and `b` the operands, `T` their common dtype and
`w` its bit width. `frac_bits`, written `f`, MUST be at least 1 and at most `w`
and `MAX_FRACTIONAL_BITS`.

| id | fn         | params              | operands         | result  | value                                                                        |
| -- | ---------- | ------------------- | ---------------- | ------- | ---------------------------------------------------------------------------- |
| 0  | `Add`      | none                | `T`, `T`         | `T`     | `a + b`, wrapping                                                            |
| 1  | `Sub`      | none                | `T`, `T`         | `T`     | `a - b`, wrapping                                                            |
| 2  | `Mul`      | none                | `T`, `T`         | `T`     | `a * b`, wrapping                                                            |
| 3  | `Divc`     | `divisor: u64`, not 0 | `T`            | `T`     | `a / divisor`, truncated toward zero                                         |
| 4  | `Div`      | none                | `T`, `T`         | `T`     | `a / b`, truncated toward zero, wrapping; fails if `b = 0`                   |
| 5  | `Lt`       | none                | `T`, `T`         | `uint8` | 1 if `a < b`, else 0                                                         |
| 6  | `Le`       | none                | `T`, `T`         | `uint8` | 1 if `a <= b`, else 0                                                        |
| 7  | `Eq`       | none                | `T`, `T`         | `uint8` | 1 if `a = b`, else 0                                                         |
| 8  | `Where`    | none                | `uint8`, `T`, `T`| `T`     | `a` if the condition is nonzero, else `b`                                    |
| 9  | `Min`      | none                | `T`, `T`         | `T`     | the smaller                                                                  |
| 10 | `Max`      | none                | `T`, `T`         | `T`     | the larger                                                                   |
| 11 | `Saturate` | `dtype: u8`         | any `T`          | `dtype` | `a` clamped to `dtype`'s range                                               |
| 12 | `QMul`     | `frac_bits: u8`     | `T`, `T`         | `T`     | `floor(a * b / 2^f)`, wrapping                                               |
| 13 | `QDiv`     | `frac_bits: u8`     | `T`, `T`         | `T`     | `a * 2^f / b`, truncated toward zero, wrapping; fails if `b = 0`             |
| 14 | `QExp`     | `frac_bits: u8`     | `T`              | `T`     | `e^(a / 2^f) * 2^f`, by the algorithm below, saturating at `T`'s maximum     |
| 15 | `QInvSqrt` | `frac_bits: u8`     | `T`              | `T`     | `floor(sqrt(floor(2^(3f) / a)))`, saturating; fails if `a <= 0`              |
| 16 | `ISqrt`    | none                | unsigned `T`     | `T`     | `floor(sqrt(a))`                                                             |

Any other fn id is invalid. Intermediate values are exact: `Div`'s and
`QDiv`'s quotients, and `QMul`'s product, are computed without overflow
before wrapping, so, for example, `Div` of `T`'s minimum by -1 is `T`'s
minimum.

`QExp` is defined by the following algorithm, not by the real exponential.
Write `a / 2^f`, with 64 fractional bits, as `k ln 2 + r` with `r` in
`[0, ln 2)`, using `ln 2` with 64 fractional bits rounded to nearest. `e^r` is
the sum of the first 21 terms of its Taylor series, evaluated by Horner's rule
with 63 fractional bits, rounding down at each step, with coefficients
`floor(2^63 / n!)`. The result is `e^r * 2^(k + f)`, rounded down, and
saturates at `T`'s maximum. A normative reference implementation will be
provided in the assets of this MIP.

### Validation

A graph's validity is a function of its code alone. A graph is valid if its
code follows the encoding above, every op and fn satisfies its validation
rules, and its memory fits the arena:

- each graph input, and each op's result other than a `Literal`'s or a
  `Reshape`'s, takes the next region of the arena, its size rounded up to a
  multiple of `ARENA_ALIGNMENT`. Regions are never reused;
- the sum of those rounded sizes MUST be at most `ARENA_SIZE`.

A `Literal`'s elements stay in the code, and a `Reshape`'s result is its
input's elements, so neither uses arena memory. Scalar nodes' registers are not
part of the arena.

Validation is a single pass over the code, linear in its length.
Implementations MAY validate a graph when it is deployed or when its code is
first loaded, and MAY keep the result of validation, the tensor types and the
arena layout as metadata.

### Evaluation

A call evaluates the graph in the code of the account it names:

1. If that code doesn't start with `GRAPH_MAGIC`, or the graph is invalid,
   the call fails.
2. The call's inputs MUST match the graph's inputs in number, and each MUST
   have exactly the dtype and shape the graph declares.
3. The ops are evaluated in order, each from the results of earlier nodes.
4. The outputs are returned or stored, as the method says.

Evaluation reads no state other than the code of the accounts that `TensorRef`
nodes and code inputs name and, for storage inputs, the caller's storage.
Implementations MAY evaluate ops and elements in any order, and MAY fuse,
split or compile them, provided the outputs and the effects on state are those
this section defines.

### Precompile interface

The precompile at `GRAPH_EVAL_ADDRESS` satisfies the following Solidity
interface:

```solidity
interface IGraphEval {
    struct TensorInput {
        uint8 dtype;
        uint16[] dimensions;
        uint8 byteOrder;
        uint8 location;
        bytes payload;
    }

    struct TensorOutput {
        uint8 byteOrder;
        uint8 location;
        bytes payload;
    }

    struct Tensor {
        uint8 dtype;
        uint16[] dimensions;
        bytes data;
    }

    function evalGraph(address graph, TensorInput[] calldata inputs)
        external returns (Tensor[] memory outputs);

    function evalGraphInto(
        address graph,
        TensorInput[] calldata inputs,
        TensorOutput[] calldata outputs
    ) external returns (Tensor[] memory returned);
}
```

The selectors are `SELECTOR_EVAL_GRAPH` and `SELECTOR_EVAL_GRAPH_INTO`.
Calldata MUST be the selector followed by the canonical ABI encoding of the
arguments, as Solidity's encoder lays it out; any other layout fails. Each
array MUST have at most `MAX_CALL_TENSORS` elements.

`byteOrder` is 0 for big-endian and 1 for little-endian. It applies to the
elements only. `location` is one of:

| location    | input payload                                                                                                             | output payload                     |
|-------------|---------------------------------------------------------------------------------------------------------------------------|------------------------------------|
| 0 (literal) | the elements, exactly the tensor's size in bytes                                                                          | empty: returned                    |
| 1 (code)    | `abi.encode(address account, uint32 offset)`: a tensor in a data account, as for `TensorRef`, its elements in `byteOrder` | not allowed                        |
| 2 (storage) | `abi.encode(uint256 slot)`: the caller's storage                                                                          | `abi.encode(uint256 slot)`: stored |

Any other `byteOrder` or `location`, or a payload of the wrong length, fails.

- `evalGraph` returns every output, in order, as `Tensor`s with big-endian
  elements.
- `evalGraphInto` MUST be given as many `TensorOutput`s as the graph has
  outputs. It stores each output whose location is storage and returns the
  others, in order, each in its `byteOrder`.

The precompile accepts `CALL`, `STATICCALL` and `DELEGATECALL`. A `CALL` MUST
send no value. `CALLCODE`, and calls through an EIP-7702 delegation to the
precompile's address, fail.

### Storage references

Storage inputs and outputs are allowed only when the precompile is called with
`DELEGATECALL`, and refer to the calling contract's own storage. Storage
outputs are not allowed in a static context.

A tensor in storage is its elements, in row-major order, each in the given
byte order, packed 32 bytes to a slot in the slots from `slot` on, modulo
2^256. Each slot's first byte is the most significant byte of its word. A
tensor of `s` bytes takes `ceil(s / 32)` slots; when it is stored, the bytes
after its elements in the last slot are zero.

Storage reads and writes are the transaction's own: they warm their slots and
count toward later accesses as `SLOAD` and `SSTORE` do, and under MIP-8, writes
are recorded for their pages. Outputs are stored after the whole graph has
been evaluated. Two stored outputs MUST NOT start at the same slot or occupy
overlapping slots. Slots whose value doesn't change are not written.

### Failure

**CLAUDE: maybe move this up so we specify what failure means before we talk about failing?**
Whenever this spec describes that the graph eval precompile "MUST fail",
the call reverts and consumes all gas given to it. A failed call makes no
changes to storage. The revert data is the same for every failure (see Open
Questions): callers cannot tell why a call failed, and implementations need not
detect failures in any particular order.

### Gas costs

The gas schedule is not yet set. Its structure:

- `G_CALL` per call.
- Loading a graph's code, and code inputs' and `TensorRef` nodes' accounts, is
  priced as a code load, as in MIP-20. For the graph's own code, that price
  also covers validation, a linear pass.
- Each op's cost is a function of its static types: per element for `Scalar`
  nodes (the sum over the node's fns of a price per fn and dtype, times the
  output's element count), `m * n * k` products for `MatMul` and `QMatMul`,
  per input element for reductions and `CumSum`, per byte for `Concat`,
  `Gather`, `TensorRef` and inputs.
- Arena memory, per byte of the graph's rounded sizes.
- Storage inputs and outputs, per slot, as `SLOAD` and `SSTORE`.

Every term except the references depends only on the graph, so a graph's
evaluation cost is a constant that validation can compute and keep. The
precompile charges it before evaluating anything.

### Chain Specifics

The precompile is activated in a future network upgrade (TBD). Before
activation, calls to `GRAPH_EVAL_ADDRESS` behave as calls to an empty account.

## Rationale

### A precompile, and graphs as code

A precompile can be called from existing contracts and toolchains without
compiler changes. Graphs live in account code because code is immutable,
addressable by `CREATE2`, priced on load by MIP-20, and needs validating only
once. The magic number's first byte, `INVALID`, keeps a graph account from
running as EVM code; data accounts use `SSTORE2`'s leading `STOP` for the
same reason. Weights beyond the code size limit are split across data
accounts and read with `TensorRef`.

### Integer dtypes of at most 64 bits

Integer arithmetic with defined rounding gives identical results on every
implementation and machine, which floating point would not. Fixed-point
fns (`QMul`, `QDiv`, `QExp`, `QInvSqrt`, `QMatMul`) state their rounding
exactly. Narrow dtypes are also where most of the speed comes from. On an AMD
Zen 4 CPU, a chain of dependent 16.16 multiplications on one `int32` costs
4.9 ns per multiplication in the reference implementation's interpreter (3.2 ns
with an experimental path for single-element `Scalar` nodes), against 6.2 ns
for the same chain in compiled EVM code and 31.7 ns in interpreted EVM code.

### Static shapes and a bounded, never-reused arena

With static shapes, validation knows every tensor's type, the whole memory
layout and all of the evaluation cost except references, before any call. The
memory rule (the sum of the results' rounded sizes) is one that a graph's
author can work out by hand. Reusing freed regions would use less memory, but
would make the allocator's choices part of consensus.

### Scalar nodes

Elementwise arithmetic is most of what graphs do, and most of it is short
chains. A `Scalar` node makes fusion part of the format: the author, not the
implementation, decides which operations run together, so a node can be
priced as one unit without promising that an optimizer will find the fusion.
Intermediate values live in the register file, not the arena, which keeps the
memory rule affordable for long chains. The register count and the 64-bit
limit on dtypes mean each register fits in a general-purpose register of
x86-64, so a node with single-element tensors can be compiled by emitting a
fixed instruction sequence per fn, with no register allocation. A prototype
template compiler built this way on asmjit took about 0.5 µs per node plus
9 to 11 ns per instruction emitted, growing linearly with the node's length,
so compiling a node is comparable to a linear analysis pass.

### A single failure outcome

Because every failure looks the same, implementations can reorder, fuse,
split and compile evaluation freely. This matches the EVM, where exceptional
halts are not distinguished.

### Storage references only under `DELEGATECALL`

A contract can then read and write only its own storage, and only through the
same accounting as `SLOAD` and `SSTORE`.

## Backwards Compatibility

This proposal adds a precompile and does not change existing behavior.
Contracts that do not call it are unaffected. Accounts whose code starts with
`fe 7f` already exist only as code that fails at once when executed.

## Test Cases

A graph with one input `x: int32[4]` and one output, `x * x + 1` in 16.16 fixed
point, as a `Scalar` node with one constant (65536) and two fns
(`QMul(16)` of registers 0 and 0 into register 2, then `Add` of registers 2
and 1):

```
fe7f00 01 06010400 01 0100 0100
00 010400 01 0000 01 0600000100 02 0c10 0000 02 00 0201
```

Without the spaces: `fe7f000106010400010100010000010400010000010600000100020c10000002000201`.

| `x` (16.16)                    | output (16.16)                  |
| ------------------------------ | ------------------------------- |
| 65536, 98304, -131072, 0       | 131072, 212992, 327680, 65536   |

These values follow from the specification and are yet to be checked against
the reference implementation. A full suite, with vectors for every op, fn and
dtype, is to be generated by the reference implementation's differential tests
and added to the assets of this MIP.

## Security Considerations

### Bounded work

Validation is linear in the graph's code. Evaluation's cost is fixed by the
graph's types, apart from references, and every fn takes a bounded number of
steps. The arena bounds a call's memory at `ARENA_SIZE` per executing thread.

### Pricing must cover the worst case

An op's cost can depend on its layout as well as its element count. In the
reference implementation, the same `int32` `QMul` over 13,520 elements took
8.54 µs or 1.71 µs depending on whether its broadcast runs were 10 or 1352
elements long. Prices set from long runs would undercharge short ones. Prices
must also assume the slowest path an attacker can force: if a faster path
(such as a compiled graph) depends on a cache, an attacker can make it miss.

### Consensus

Every result is defined exactly, over each dtype's whole range. An
implementation that diverges on any input splits the network, so
implementations should be tested differentially against each other and the
reference algorithms, over every op, fn and dtype.

### References

`TensorRef` nodes and code inputs can name any account. Their reads are priced
as code loads. Storage writes happen only under `DELEGATECALL`, only to the
caller's own storage, never in a static context, and only after the whole
graph has been evaluated, so a failed call writes nothing.

## Open Questions

- **Gas constants,** and whether `Scalar` nodes are priced at interpreted
  speed, or at compiled speed with compilation promised as a linear
  pre-processing pass.
- **Layout-dependent costs:** whether prices depend on run lengths, which are
  known at validation.
- **Validation at deployment:** whether deploying code that starts with `fe 7f`
  but is not a valid graph should fail.
- **The failure's revert data:** empty, or a single fixed error.
- **Storage layout:** whether a stored tensor starts with a length slot. Without
  one, a model's tensors fit MIP-8 pages more tightly.
- **Byte orders in code:** `TensorRef` elements are always little-endian, while
  code inputs use the input's `byteOrder`.
- **`MatMul` dtypes:** only `int8` today.
- **`ArgMin` and `ArgMax`'s result dtype:** the input's, so an index wraps for
  a narrow dtype with many elements.
- **Constants in Scalar nodes:** a constant pool, as specified, or a fn that
  writes a constant to a register.
- **Destinations aliasing operands:** allowed, as specified, or forbidden.

## Copyright

Copyright and related rights waived via [CC0](../LICENSE.md).
