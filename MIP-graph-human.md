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

Add a precompile at address `0x1002` that evaluates a graph of tensor
operations. A graph is stored as the code of an ordinary account, in a
compact binary format. Graphs support a fixed set of tensor operations
on signed and unsigned integer types at most 64 bits wide, with no
support for control flow, side effects, floating point or dynamic
shapes. Callers pass the graph's inputs by value or by reference to an
account's code, and receive the outputs back.

## Motivation

Numeric work in EVM code is expensive. Every value is a 256-bit word,
so a 32-bit multiplication with wrapping takes a multiplication and a
sign extension, and a 16.16 fixed-point multiplication takes eight
opcodes and 30 gas. Loops over arrays pay for bounds checks, loop
control and memory or storage accesses on every element. Workloads
that run the same arithmetic over many values, or long chains of
narrow integer arithmetic, such as inference with quantized neural
networks, order matching, pricing curves and simulations, cost far
more in gas than the work they do. For example, a small MNIST digit
classifier (an 8-filter convolution, max pooling and a dense layer of
13,520 `int16` weights) written in Solidity uses 10.4 million gas per
prediction and takes 1.15 ms in compiled EVM code. The same model, as a
graph, takes about 23 µs in the reference implementation's interpreter.

A precompile that takes a whole computation as one graph of tensor
operations can execute it with machine-width integer arithmetic,
without per-element dispatch. Because the graph is fixed in advance,
its validity, memory use and most of its cost are known before it
runs, which allows implementations to validate and compile graphs
before execution.

## Specification

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.ietf.org/rfc/rfc2119.html) and [RFC 8174](https://www.ietf.org/rfc/rfc8174.html).

### Constants

| Name                       | Value                        |
|----------------------------|------------------------------|
| `GRAPH_EVAL_ADDRESS`       | `0x1002`                     |
| `GRAPH_MAGIC`              | the bytes `0xef 0x7f`        |
| `GRAPH_VERSION`            | `1`                          |
| `MAX_GRAPH_INPUTS`         | `8`                          |
| `MAX_GRAPH_OUTPUTS`        | `8`                          |
| `MAX_GRAPH_OPS`            | `16 * 1024`                  |
| `MAX_RANK`                 | `8`                          |
| `MAX_DIM`                  | `65535`                      |
| `MAX_SCALAR_INPUTS`        | `8`                          |
| `MAX_SCALAR_REGISTERS`     | `14`                         |
| `MAX_SCALAR_FNS`           | `255`                        |
| `ARENA_SIZE`               | 64 MiB                       |
| `ARENA_ALIGNMENT`          | `64`                         |
| `SELECTOR_EVAL_GRAPH`      | `0xd259ffd8`                 |

### Graphcode

#### Tensors, Shapes and Types

A tensor's type consists of a shape (a list of dimension sizes) and a dtype (the type of its elements).

Tensor types conform to the following schema, written in FlatBuffers-like notation. All
numeric types are little-endian, and all data structures are stored without padding
or alignment.

```
enum Dtype:uint8 {
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Int8,
    Int16,
    Int32,
    Int64
}

struct Shape {
    rank: uint8;                // 0 <= rank <= MAX_RANK
    dimensions: [uint16:rank];  // 0 <= dimensions[i] <= MAX_DIM
}

struct Type {
    dtype: Dtype;
    shape: Shape;
}
```

`Uint8` to `Uint64` are unsigned and `Int8` to `Int64` are signed, in two's
complement. $\mathrm{byte\_width}$ is 1 for `Uint8` and `Int8`, 2 for `Uint16`
and `Int16`, 4 for `Uint32` and `Int32`, and 8 for `Uint64` and `Int64`, and
$\mathrm{bit\_width} = 8 \times \mathrm{byte\_width}$.

Given a shape $s$, we define $\mathrm{size}(s) = \prod_i s.\mathrm{dimensions}[i]$ and require that valid shapes satisfy
$\mathrm{size}(s) < 2^{64}$.

Given a tensor type $t$, we define $\mathrm{byte\_size}(t) = \mathrm{size}(t.\mathrm{shape}) \times \mathrm{byte\_width}(t.\mathrm{dtype})$ and require
that valid tensor types satisfy $\mathrm{byte\_size}(t) < 2^{64}$.

A tensor's elements are ordered row-major: the last dimension varies fastest.

#### Graphcode Definition

Graphcode is the compact on-chain representation of a computation graph. It is deployed and stored as
regular contract code that starts with the magic bytes
`0xef 0x7f` and invoked indirectly via a call to the `evalGraph` endpoint described in
[Precompile Interface](#precompile-interface).

Valid graphcode conforms to the following schema, written in FlatBuffers-like notation and without trailing bytes.

```
struct NodeId {
    value: uint16;
}

struct Graph {
    magic: [uint8:2];            // magic == GRAPH_MAGIC
    version: uint8;              // version == GRAPH_VERSION
    n_inputs: uint8;             // 0 <= n_inputs <= MAX_GRAPH_INPUTS
    inputs: [Type:n_inputs];
    n_outputs: uint8;            // 0 <= n_outputs <= MAX_GRAPH_OUTPUTS
    outputs: [NodeId:n_outputs];
    n_ops: uint16;               // 0 <= n_ops <= MAX_GRAPH_OPS
    ops: [Op:n_ops];
}
```

Graphcode encodes a computation graph as a list of topologically ordered nodes, numbered from 0 to
`n_inputs + n_ops - 1`. Nodes 0 to `n_inputs - 1` are the graph's inputs, with node `n_inputs`
corresponding to `ops[0]`, `n_inputs+1` corresponding to `ops[1]` and so forth.

Each entry in `outputs` MUST be a node id below `n_inputs + n_ops`. An output may be a graph input, and the
same node may appear more than once in `outputs`.

#### Operation Definition

The `ops` list in a graph definition contains the operation nodes.
Each operation node consists of an opcode, a list of operation-specific parameters and a list of inputs which
MUST match the arity of the operation. Each input is provided as a node id, and
MUST refer only to previous nodes (either inputs or operations). That is, the inputs of `ops[i]` MUST
be in the range `[0, n_inputs + i)`.

```
struct Op {
    opcode: Opcode;
    params: PARAMETERS(opcode);
    inputs: [NodeId:ARITY(opcode)];
}

enum Opcode: uint8 {
    Scalar = 0,
    Literal,
    TensorRef,
    Reshape,
    Transpose,
    Concat,
    QMatMul,
    CumSum,
    ArgMin,
    ArgMax,
    ReduceSum,
    ReduceMax,
    Gather
}
```

Any other opcode is invalid. The parameters and arity of each opcode are as described below, with the
exception of `Scalar` nodes which are specified in
[Scalar Definition](#scalar-definition). In the comments, `X` is an operation's first input.

* `Literal`

```
struct PARAMETERS(Literal) {
    type: Type;
    elements: [uint8:byte_size(type)];   // row-major, each element little-endian
}

ARITY(Literal) = 0
```

* `TensorRef`

```
struct PARAMETERS(TensorRef) {
    type: Type;
    address: [uint8:20];
    offset: uint32;
}

ARITY(TensorRef) = 0
```

* `Reshape`

```
struct PARAMETERS(Reshape) {
    shape: Shape;
}

ARITY(Reshape) = 1
```

* `Transpose`

```
struct PARAMETERS(Transpose) {
    axis0: uint8;   // axis0 < rank(X)
    axis1: uint8;   // axis1 < rank(X)
}

ARITY(Transpose) = 1
```

* `Concat`

```
struct PARAMETERS(Concat) {
    axis: uint8;   // axis < rank(X)
}

ARITY(Concat) = 2
```

* `QMatMul`

```
struct PARAMETERS(QMatMul) {
    frac_bits: uint8; // 0 <= frac_bits <= 64
    out_dtype: Dtype;
}

ARITY(QMatMul) = 2
```

* `CumSum`, `ReduceSum` and `ReduceMax`

```
struct PARAMETERS(CumSum) {
    axis: uint8;   // axis < rank(X)
}

ARITY(CumSum) = 1
```

`ReduceSum` and `ReduceMax` have the same parameters and arity as `CumSum`.

* `ArgMin` and `ArgMax`

```
struct PARAMETERS(ArgMin) {
}

ARITY(ArgMin) = 1
```

`ArgMax` has the same parameters and arity as `ArgMin`.

* `Gather`

```
struct PARAMETERS(Gather) {
    axis: uint8;   // axis < rank(X)
}

ARITY(Gather) = 2   // values X, then indices I
```

#### Scalar Definition

A `Scalar` node computes every element of its output with the same short program: a list of
functions (fns) operating on a finite set of `MAX_SCALAR_REGISTERS` registers. Instead of having a fixed
arity, its parameters determine the number and node ids of its inputs.

```
struct PARAMETERS(Scalar) {
    output_shape: Shape;
    n_inputs: uint8;                     // 0 <= n_inputs <= MAX_SCALAR_INPUTS
    inputs: [NodeId:n_inputs];           // registers 0 to n_inputs - 1
    n_constants: uint8;                  // n_inputs + n_constants <= MAX_SCALAR_REGISTERS
    constants: [Constant:n_constants];   // registers n_inputs to n_inputs + n_constants - 1
    n_fns: uint8;                        // 1 <= n_fns <= MAX_SCALAR_FNS
    fns: [Fn:n_fns];
}

ARITY(Scalar) = 0

struct Constant {
    dtype: Dtype;
    value: [uint8:byte_width(dtype)];    // little-endian
}

struct Fn {
    fn: FnId;
    params: FN_PARAMETERS(fn);
    operands: [uint8:FN_ARITY(fn)];      // register numbers
    destination: uint8;                  // a register number; omitted for the last fn
}

enum FnId: uint8 {
    Add = 0,
    Sub,
    Mul,
    Divc,
    Div,
    Lt,
    Le,
    Eq,
    Where,
    Min,
    Max,
    Saturate,
    QMul,
    QDiv,
    QExp,
    QInvSqrt,
    ISqrt
}
```

Any other fn id is invalid. The parameters and arity of each fn:

| Fn                                                         | `FN_PARAMETERS`              | `FN_ARITY` |
|------------------------------------------------------------|------------------------------|------------|
| `Add`, `Sub`, `Mul`, `Div`, `Lt`, `Le`, `Eq`, `Min`, `Max` | none                         | 2          |
| `Divc`                                                     | `divisor: uint64` (not 0)    | 1          |
| `Where`                                                    | none                         | 3          |
| `Saturate`                                                 | `dtype: Dtype`               | 1          |
| `QMul`, `QDiv`                                             | `frac_bits: uint8`           | 2          |
| `QExp`, `QInvSqrt`                                         | `frac_bits: uint8`           | 1          |
| `ISqrt`                                                    | none                         | 1          |

A `Scalar` node is valid if, in addition:

- Each of `inputs` refers only to previous nodes, as an op's inputs do.
- Each input broadcasts to `output_shape`: its rank is at most `output_shape`'s, and, matching
  dimensions from the last, each of its dimensions is 1 or equal to `output_shape`'s.
- Every operand is a register below `MAX_SCALAR_REGISTERS` that holds a value at that point: an
  input, a constant, or the destination of an earlier fn.
- Every destination is at least `n_inputs + n_constants` and below `MAX_SCALAR_REGISTERS`, so input
  and constant registers are never written. A destination may be one of the fn's own operands.
- Every fn's operands have a dtype combination listed for it in [Scalar Evaluation](#scalar-evaluation).
  An input register has its input's dtype, a constant register its constant's dtype, and a
  destination the result dtype of the fn that last wrote it.
- Every `QMul`, `QDiv`, `QExp` and `QInvSqrt` fn's `frac_bits` is at most $\mathrm{bit\_width}(T)$,
  where $T$ is the dtype of the fn's operands.

The node's output type is `output_shape` with the result dtype of the last fn.

#### Memory

Each graph input, and the output of each op other than a `Literal` or a `Reshape`, takes the next
region of an arena, its size the output type's byte size rounded up to a multiple of
`ARENA_ALIGNMENT`. Regions are never reused. In valid graphcode, the sum of those rounded sizes is
at most `ARENA_SIZE`.

A `Literal`'s elements stay in the code, and a `Reshape`'s output is its input's elements, so neither
uses arena memory. A `Scalar` node's registers are not part of the arena. The "Allocates" line of
each op in [Operation Evaluation](#operation-evaluation) says whether its output takes a region.

### Deploying Graphcode

Graphcode is deployed as the code of an ordinary account, by a contract-creation transaction,
`CREATE` or `CREATE2`, subject to the usual code size limit and TBD code deposit cost.

[EIP-3541](https://eips.ethereum.org/EIPS/eip-3541) makes contract creation fail when the code it
would deploy starts with the byte `0xef`. This MIP adds one exception: creation does not fail for
that reason when the code starts with `GRAPH_MAGIC`. Code that starts with `0xef` followed by any
other byte is still rejected. Whether creation should also fail when code that starts with
`GRAPH_MAGIC` is not valid graphcode is an open question (see [Open Questions](#open-questions)).

`0xef` is not a defined opcode, so a call that executes graphcode as EVM code fails at once.

Tensors that `TensorRef` nodes and code inputs read are also stored in account code. A tensor can be
at any offset of any account's code, including a graph's, encoded as a `Literal` node's parameters:
its `Type`, then its elements. A reference to it is the account's address and the byte offset of the
encoding, counted from the code's first byte.

### Precompile Interface

The precompile at `GRAPH_EVAL_ADDRESS` satisfies the following Solidity interface:

```solidity
interface IGraphEval {
    struct TensorType {
        uint8 dtype;
        uint16[] dimensions;
    }

    enum Location { Literal, CodeRef }

    struct TensorInput {
        TensorType ty;
        Location location;
        bytes payload;
    }

    struct Tensor {
        TensorType ty;
        bytes data;
    }

    function evalGraph(address graph, TensorInput[] calldata inputs)
        external returns (Tensor[] memory outputs);
}
```

The selector of `evalGraph` is `SELECTOR_EVAL_GRAPH`. Calldata must be the selector followed by the
canonical ABI encoding of the arguments, as Solidity's encoder lays it out; any other layout fails.

**TODO for self: rewrite this**
In a `TensorInput` declaration, `byteOrder` is 0 for big-endian and 1 for little-endian, and applies to the elements only. `location` is one of:

| `location` | `payload`                                                                                            |
|------------|------------------------------------------------------------------------------------------------------|
| Literal    | the tensor's elements                                                                                |
| TensorRef  | `abi.encode(address account, uint32 offset)`: a tensor in `account`'s code, as in the `TensorRef` op |

A payload of the wrong length for the provided `location` and `ty` causes the call to fail.

`evalGraph` returns the graph's outputs, in the order of its `outputs` list, as `Tensor`s whose
elements are big-endian.

The precompile MUST be invoked via `CALL` that sends no value.
`STATICCALL`, `DELEGATECALL`, `CALLCODE`, and calls through an
[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702) delegation to the precompile's address MUST fail,
as with the MIP-4 reserve balance introspection precompile.

### Precompile Evaluation

A call to `evalGraph(graph, inputs)` evaluates the graphcode in the code of the account `graph`:

1. The code of `graph` MUST be valid graphcode according to the conditions in [Graphcode](#graphcode).
2. `inputs` MUST have exactly `graph.n_inputs` elements. For each `i`, the type `inputs[i].ty`
   MUST be equal to `graph.inputs[i]`.
3. The ops are evaluated in order, each from the outputs of earlier nodes, as
   [Operation Evaluation](#operation-evaluation) describes.
4. The call returns the values of the nodes in `graph.outputs`.

Evaluation reads no state other than the code of `graph` and of the accounts that `TensorRef` nodes
and code inputs name, and writes none. Implementations MAY evaluate ops and elements in any order,
and MAY fuse, split or compile them, provided the outputs are those this section defines.

#### Failure

Every failure condition in this specification must be checked, including in nodes whose outputs
are unused. Implementations MAY check conditions before or during evaluation, in any order, provided
they preserve the specified success or failure outcome.

A failed call reverts and consumes all gas given to it. The revert data is the same for every
failure (see [Open Questions](#open-questions)): callers cannot tell why or when a call failed, and
implementations need not detect failures in any particular order.

#### Operation Evaluation

$\mathrm{wrap}_T(v)$ is the value of dtype $T$ that is congruent to the integer $v$ modulo
$2^{\mathrm{bit\_width}(T)}$. Sums and products below are of exact integers, and wrap only where
stated. $T$ stands for any dtype. "Allocates" says whether the op's output takes a region of the
arena (see [Memory](#memory)).

* `Literal`

`Literal<type, elements>()` is the tensor of type `type` whose elements, in row-major order, are read
from `elements`, each `byte_width(type.dtype)` bytes, little-endian.

Valid type combinations:

| Out          |
|--------------|
| `type.dtype` |

Valid shape combinations:

| Out          |
|--------------|
| `type.shape` |

Allocates: no.

* `TensorRef`

`TensorRef<type, address, offset>()` is the tensor at `offset` in the code of `address` (see
[Deploying Graphcode](#deploying-graphcode)), its elements little-endian. The call fails if the
tensor's encoding, its `Type` followed by its elements, extends past the end of the code, or if that
`Type` differs from `type`.

Valid type combinations:

| Out          |
|--------------|
| `type.dtype` |

Valid shape combinations:

| Out          |
|--------------|
| `type.shape` |

Allocates: yes.

* `Reshape`

`Reshape<shape>(X)` has $X$'s elements, in the same row-major order, and the shape `shape`.

Valid type combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X   | Out     |
|-----|---------|
| `s` | `shape` |

with $\mathrm{size}(s) = \mathrm{size}(\texttt{shape})$.

Allocates: no.

* `Transpose`

`Transpose<axis0, axis1>(X)` swaps dimensions `axis0` and `axis1` of $X$: each output element is the
element of $X$ whose coordinates are the output element's, with the coordinates along `axis0` and
`axis1` exchanged. For a matrix and axes 0 and 1, $\mathrm{Out}[i, j] = X[j, i]$. If `axis0` equals
`axis1`, the output is $X$.

Valid type combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X                         | Out                       |
|---------------------------|---------------------------|
| `[p..., a, q..., b, r...]` | `[p..., b, q..., a, r...]` |

where `a` and `b` are the dimensions along `axis0` and `axis1`, in either order.

Allocates: yes.

* `Concat`

`Concat<axis>(X, Y)` joins $X$ and $Y$ along `axis` starting with $X$.

Valid type combinations:

| X   | Y   | Out |
|-----|-----|-----|
| `T` | `T` | `T` |

Valid shape combinations:

| X              | Y              | Out                |
|----------------|----------------|--------------------|
| `[p..., a, q...]` | `[p..., b, q...]` | `[p..., a + b, q...]` |

where `p...` denotes the sequence of dimensions preceding `axis`, and $a + b \le$ `MAX_DIM`.

Allocates: yes.

* `QMatMul`

`QMatMul<frac_bits, out_dtype>(X, Y)` multiplies $X$ by the transpose of $Y$ exactly, then shifts
each sum right by `frac_bits`, rounding toward negative infinity, and wraps it to `out_dtype`:

$$\mathrm{Out}[i, j] = \mathrm{wrap}_{\mathrm{out\_dtype}}\left( \left\lfloor \frac{1}{2^{\mathrm{frac\_bits}}} \sum_{l=0}^{k-1} X[i, l] \cdot Y[j, l] \right\rfloor \right)$$

Every output element is the dot product of a row of $X$ and a row of $Y$.

Valid type combinations:

| X   | Y   | Out         |
|-----|-----|-------------|
| `T` | `T` | `out_dtype` |

Valid shape combinations:

| X        | Y        | Out      |
|----------|----------|----------|
| `[m, k]` | `[n, k]` | `[m, n]` |

Allocates: yes.

* `CumSum`

`CumSum<axis>(X)` sums $X$ along `axis`: each output element is $\mathrm{wrap}_T$ of the sum of $X$'s
elements at its position and every earlier position along `axis`, with the other coordinates the
same.

Valid type combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X   | Out |
|-----|-----|
| `s` | `s` |

Allocates: yes.

* `ArgMin` and `ArgMax`

`ArgMin(X)` is $\mathrm{wrap}_T(n)$, where $n$ is the row-major index of the first smallest element of
$X$. `ArgMax(X)` is the same for the first largest element.

Valid type combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X   | Out  |
|-----|------|
| `s` | `[]` |

with $\mathrm{size}(s) \ge 1$.

Allocates: yes.

* `ReduceSum` and `ReduceMax`

`ReduceSum<axis>(X)` sums $X$ along `axis`: each output element is $\mathrm{wrap}_T$ of the sum of
$X$'s elements along `axis` with the same other coordinates. `ReduceMax<axis>(X)` is the largest of
them instead.

Valid type combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X                 | Out               |
|-------------------|-------------------|
| `[p..., a, q...]` | `[p..., 1, q...]` |

where `p...` are the `axis` dimensions before `axis`, and $a \ge 1$.

Allocates: yes.

* `Gather`

`Gather<axis>(X, I)` takes elements of $X$ along `axis` at the positions $I$ gives:
$\mathrm{Out}[p, r, q] = X[p, I[r], q]$, where $p$ stands for the coordinates before `axis`, $r$ for
$I$'s coordinates and $q$ for the coordinates after `axis`. The call fails if any element of $I$ is
negative or at least $a$.

Valid type combinations:

| X   | I               | Out |
|-----|-----------------|-----|
| `T` | any dtype       | `T` |

Valid shape combinations:

| X                 | I      | Out                  |
|-------------------|--------|----------------------|
| `[p..., a, q...]` | `[r...]` | `[p..., r..., q...]` |

where `p...` are the `axis` dimensions before `axis`, and the output's rank is at most `MAX_RANK`.

Allocates: yes.

* `Scalar`

See [Scalar Evaluation](#scalar-evaluation).

Allocates: yes.

#### Scalar Evaluation

A `Scalar` node computes each element of its output independently:

1. Each input register holds the input's element that corresponds to the output element: matching
   dimensions from the last, the input's coordinate along each dimension is 0 where the input's
   dimension is 1, and the output element's coordinate otherwise.
2. Each constant register holds its constant.
3. The fns run in order. Each reads its operands, then writes its result to its destination, so a
   destination that is also an operand is read before it is written.
4. The last fn's result is the output element.

The fns, with $a$ and $b$ the operands (for `Where`, $c$, $a$ and $b$), $T$ their dtype, and $f$ the
fn's `frac_bits`:

| Fn         | Operands          | Result   | Value                                                                                  |
|------------|-------------------|----------|----------------------------------------------------------------------------------------|
| `Add`      | `T`, `T`          | `T`      | $\mathrm{wrap}_T(a + b)$                                                               |
| `Sub`      | `T`, `T`          | `T`      | $\mathrm{wrap}_T(a - b)$                                                               |
| `Mul`      | `T`, `T`          | `T`      | $\mathrm{wrap}_T(a \cdot b)$                                                           |
| `Divc`     | `T`               | `T`      | $a / \mathrm{divisor}$, truncated toward zero                                          |
| `Div`      | `T`, `T`          | `T`      | $\mathrm{wrap}_T(a / b)$, truncated toward zero; fails if $b = 0$                      |
| `Lt`       | `T`, `T`          | `Uint8`  | 1 if $a < b$, else 0                                                                   |
| `Le`       | `T`, `T`          | `Uint8`  | 1 if $a \le b$, else 0                                                                 |
| `Eq`       | `T`, `T`          | `Uint8`  | 1 if $a = b$, else 0                                                                   |
| `Where`    | `Uint8`, `T`, `T` | `T`      | $a$ if $c \ne 0$, else $b$                                                             |
| `Min`      | `T`, `T`          | `T`      | the smaller of $a$ and $b$                                                             |
| `Max`      | `T`, `T`          | `T`      | the larger of $a$ and $b$                                                              |
| `Saturate` | `T`               | `dtype`  | $a$ clamped to the range of `dtype`                                                    |
| `QMul`     | `T`, `T`          | `T`      | $\mathrm{wrap}_T(\lfloor a \cdot b / 2^f \rfloor)$                                     |
| `QDiv`     | `T`, `T`          | `T`      | $\mathrm{wrap}_T(a \cdot 2^f / b)$, truncated toward zero; fails if $b = 0$            |
| `QExp`     | `T`               | `T`      | $e^{a / 2^f} \cdot 2^f$ by the algorithm below, saturating at $T$'s maximum            |
| `QInvSqrt` | `T`               | `T`      | $\lfloor \sqrt{\lfloor 2^{3f} / a \rfloor} \rfloor$, saturating; fails if $a \le 0$    |
| `ISqrt`    | unsigned `T`      | `T`      | $\lfloor \sqrt{a} \rfloor$                                                             |

Intermediate values are exact: `Div`'s and `QDiv`'s quotients and `QMul`'s product are computed
without overflow before wrapping, so, for example, `Div` of the `Int8` value $-128$ by $-1$ is
$\mathrm{wrap}_{\mathrm{Int8}}(128) = -128$.

#### `QExp` semantics

`QExp` is defined by the following algorithm, not by the real exponential. It writes $a / 2^f$ as
$k \ln 2 + r$, with $r$ in $[0, \ln 2)$, sums the first 21 terms of the Taylor series of $e^r$ by
Horner's rule, and multiplies the sum by $2^{k + f}$. All arithmetic is exact, with no overflow, and
`floor` rounds toward negative infinity.

```
QExp(a, f):                        // a of dtype T, 0 <= f <= bit_width(T)
    LN2 = 0xb17217f7d1cf79ac       // ln 2 with 64 fractional bits, rounded to nearest
    C[n] = floor(2^63 / n!)        // for 0 <= n <= 20: 1 / n! with 63 fractional bits
    v = a * 2^(64 - f)             // a / 2^f with 64 fractional bits
    k = floor(v / LN2)
    r = v - k * LN2                // 0 <= r < LN2
    s = floor(r / 2)               // r with 63 fractional bits
    p = C[20]
    for n = 19 down to 0:          // p ends as e^r with 63 fractional bits
        p = C[n] + floor(p * s / 2^63)
    return min(floor(p * 2^(k + f - 63)), max_T)   // max_T is T's maximum
```

A normative reference implementation will be provided in the assets of this MIP.

### Gas Costs

The gas schedule is not yet set, but we outline a general structure here.

- A fixed base cost per call.
- Reading `TensorRef` call inputs, priced as a MIP-20 code load.
- Per-op gas costs computed as a function of the input shapes and dtypes, with each operation
  defining its own cost function.
  - `Scalar` nodes price in a flat cost, an extra for any input that needs broadcasting, and
    a per-fn gas cost paid for each output element, for a total fee of
    $$G_{opcode} + G_{inputbroadcasting} + (\sum_i G_{fns[i]}) \times size(output)$$
    It is likely that an efficient pricing scheme will involve fractional gas costs for cheap fns.
- Arena memory, per byte of the graph's allocated memory size (see [Memory](#memory)).

Every term except the code loads of the accounts a graph references depends only on the graph's
code, so an implementation can compute a graph's cost once and keep it. A call whose gas does not
cover the cost fails.

## Rationale

### A precompile, and graphs as code

A precompile can be called from existing contracts and toolchains without compiler changes. Graphs
live in account code because code is immutable, addressable by `CREATE2`, priced on load by MIP-20,
and can be validated once.

### The magic bytes

Graphcode's header follows the one that
[EIP-3540](https://eips.ethereum.org/EIPS/eip-3540) proposes for EVM Object Format (EOF) contracts:
two magic bytes starting with `0xef`, then a version byte. EOF's magic is `0xef 0x00`, and
graphcode's is `0xef 0x7f`. As in EIP-3540, the first version is 1.
[EIP-3541](https://eips.ethereum.org/EIPS/eip-3541) reserved code starting with `0xef` for such
formats, which [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702)'s delegation indicator `0xef0100` also uses. Because of it, no account on
Monad has code starting with `0xef 0x7f`, so no existing contract can be mistaken for graphcode, and
graphcode run as EVM code fails at once.

### Tensors in any account's code

Tensors need no marker of their own: they can be read from any offset of any account's code, so a
graph's `Literal` can be shared with other graphs, and weights beyond the code size limit can be split
across several accounts. An account whose code starts with a tensor still stops or fails at once if
called, because its first byte is a dtype id: 0 is `STOP`, and 1 to 7 are arithmetic opcodes that
fail on an empty stack.

### Integer dtypes of at most 64 bits

Integer arithmetic with defined rounding gives identical results on every implementation and
machine, which floating point would not. The fixed-point fns (`QMul`, `QDiv`, `QExp`, `QInvSqrt`)
and `QMatMul` state their rounding exactly. Narrow dtypes are also where most of the speed comes
from. On an AMD Zen 4 CPU, a chain of dependent 16.16 multiplications on one `int32` costs 4.9 ns
per multiplication in the reference implementation's interpreter (3.2 ns with an experimental path
for single-element `Scalar` nodes), against 6.2 ns for the same chain in compiled EVM code and
31.7 ns in interpreted EVM code.

### One matrix multiplication, with its second operand transposed

`QMatMul` with `frac_bits` 0 is an exact integer matrix product, wrapped to `out_dtype`, so a separate
`MatMul` is not needed: with `Int8` inputs and an `Int32` output, no sum can wrap, since each sum is
at most $65535 \cdot 2^{14} < 2^{31}$ in magnitude. Taking $Y$ transposed makes every output element
the dot product of two rows, both contiguous in memory, and matches the layout in which PyTorch
stores a linear layer's weights (output features by input features).

### Static shapes and a bounded, never-reused arena

**TODO SELF: rewrite**
With static shapes, every tensor's type, the whole memory layout and all of the evaluation cost
except references follow from the graph's code, so an implementation can work them out before any
call. The memory usage of a graph can be worked out by hand by the author (the sum of the outputs' rounded sizes) is one that a graph's author can work
out by hand. Reusing freed regions would use less memory, but would make the allocator's choices part
of consensus.

### Scalar nodes

Elementwise arithmetic is common and easy to optimize; an implementation may, for example, choose
to AOT-compile long chains of elementwise operations into compact blocks of SIMD instructions.
Unlike whole-tensor operations such as matrix multiplication, elementwise operations can be streamed
over input tensors without ever materializing intermediate results, reducing memory pressure.
Reifying elementwise pipelines into `Scalar` nodes serves two purposes:
* It reduces memory usage of many common graphs by guaranteeing that implementations can stream execution
  without relying on complex analysis passes.
* It makes it easier for implementations to optimize aggressively. The register count and the 64-bit
  limit on dtypes mean each graph register fits in a general-purpose register of x86-64, so a node with
  single-element tensors can be compiled by emitting a fixed instruction sequence per fn, effectively
  moving register allocation off the hot path. A prototype template compiler built this way on asmjit
  took about 0.5 µs per node plus 9 to 11 ns per instruction emitted.

### No storage access

Graphcode has no storage-access operations. A contract that keeps tensors in storage must read
them with `SLOAD` and pass them as literal inputs, and then store the outputs with `SSTORE`.

An earlier draft also let a call refer to the caller's storage, allowing inputs and outputs to
be passed by reference to the caller's storage. That design would let storage accesses be priced
more cheaply. A contract pays the [EIP-2929](https://eips.ethereum.org/EIPS/eip-2929) cold access cost for every slot it reads or writes, even under
MIP-8, which charges an `SSTORE`'s page write once per page. A precompile that
knows in advance every slot a call reads and writes could instead charge for access once per page,
without extending the EVM with page-level storage operations. This approach was left out to minimize
complexity but can be added later as a new endpoint, with no change to graphcode.

### A single failure outcome

Because every failure looks the same, implementations can reorder, fuse, split and compile
evaluation freely, and can check validity ahead of time or during evaluation. This matches the EVM,
where exceptional halts are not distinguished.

## Backwards Compatibility

This MIP takes up a new precompile address, `0x1002`, which had no code. Calls to it that used to
succeed as calls to an empty account now evaluate a graph, and fail unless their calldata is a valid
`evalGraph` call.

Before this MIP, [EIP-3541](https://eips.ethereum.org/EIPS/eip-3541) made deploying any code starting
with `0xef` fail. Since `0xef 0x7f` is now a valid contract header, deploying such a contract no
longer fails.

## Security Considerations

### Bounded work

The cost of validation is linear in the length of the graph's code. The
code deposit cost for graphcode should be chosen so that repeatedly deploying
large graphs is not a DoS opportunity.

Graphs have no control flow operators and no means of performing calls, so
execution time is always bounded. Memory usage within each call is also bounded
by `ARENA_SIZE`.

### Pricing must cover the worst case

An operation's cost is not proportional to its element count alone. In the
reference implementation's interpreter, an `int32` `QMul` costs about 4.9 ns
when its node's tensors have one element, most of it decoding and dispatching
the fn, which a node over many elements pays once for a block of elements
rather than once for each. Prices set from large tensors would undercharge
small ones, which is why `Scalar` nodes have a price per node as well as per
element. Prices must also assume the slowest path an attacker can force.

Cache effects matter too. The arena can be larger than a CPU's caches,
`TensorRef` nodes and code inputs read code that may be in no cache, and
`Gather` reads elements at positions that the call's data chooses. The time
an element takes depends on where its data is, and an attacker can arrange for
it to be in main memory, so prices should be set from measurements with cold
caches and tensors as large as the arena allows.

### Consensus

Every result is defined exactly over each dtype's whole range. An
implementation that diverges on any input splits the network, so implementations
should be tested differentially against each other and the reference algorithms,
over every op, fn and dtype.

### References

`TensorRef` nodes and code inputs can name any account. Their reads are priced
as code loads. The precompile writes no state, so a call, failed or not, does
not touch storage.

## Open Questions

- **Operation list:** the list of operations and functions provided
  here is a WIP and was selected to cover a number of illustrative
  examples.
- **Gas cost numbers:** gas costs should be picked based on
  worst-case measurements for supported operations and dtypes.
- **Validation at deployment:** whether deploying code that starts
  with `0xef 0x7f` but is not a valid graph should fail.
- **Revert data on failure:** whether to leave it empty or provide
  minimal error information (without compromising implementations'
  freedom to detect failures in any order).

## Copyright

Copyright and related rights waived via CC0.
