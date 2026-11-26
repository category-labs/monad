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

Add a precompile at address `0x1002` that evaluates a graph of tensor operations. A graph is stored
as the code of an ordinary account, in a compact binary format. Graphs support a fixed set of tensor
operations on signed and unsigned integer types at most 64 bits wide, with no support for control
flow, side effects, floating point or dynamic shapes. Callers pass the graph's inputs by value or by
reference to an account's code, and receive the outputs.

## Motivation

Numeric work in EVM code is expensive. Every value is a 256-bit word, so a 32-bit multiplication
with wrapping takes a multiplication and a sign extension, and a 16.16 fixed-point multiplication
takes eight opcodes and 30 gas. Loops over arrays pay for bounds checks, loop control and memory or
storage accesses on every element. Workloads such as inference with quantized neural networks, order
matching, pricing curves and simulations repeat the same arithmetic over many values or evaluate
long chains of narrow integer operations, so most of the gas they use pays for this overhead rather
than for the arithmetic. For example, a small MNIST digit classifier (an 8-filter convolution, max
pooling and a dense layer with 13,520 `int16` weights) written in Solidity uses 10.4 million gas per
prediction and takes 1.15 ms in compiled EVM code. The same model, as a graph, takes about 23 µs in
the reference implementation's interpreter.

A precompile that takes a whole computation as one graph of tensor operations can execute it
efficiently with machine-width integer arithmetic. Because the graph is fixed in advance, its
validity, memory use and most of its cost are known before it runs, so implementations can validate
and compile graphs ahead of time.

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
| `MAX_CONCAT_INPUTS`        | `16`                         |
| `MAX_SCALAR_INPUTS`        | `8`                          |
| `MAX_SCALAR_REGISTERS`     | `14`                         |
| `MAX_SCALAR_FNS`           | `255`                        |
| `ARENA_SIZE`               | 64 MiB                       |
| `ARENA_ALIGNMENT`          | `64`                         |
| `SELECTOR_EVAL_GRAPH`      | `0x7b1da75f`                 |

### Graphcode

#### Tensors, Shapes and Types

A tensor's type consists of a shape (a list of dimension sizes) and a dtype (the type of its elements).

Tensor types conform to the following schema, written in FlatBuffers-like notation. All
multibyte numeric fields in graphcode are stored in little-endian order. All data structures are packed
without padding or alignment.

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

`Uint8` to `Uint64` are unsigned types of the corresponding bit width. `Int8` to `Int64` are signed
types of the corresponding bit width, stored in two's complement. $\mathrm{byte\_width}$ is 1 for
`Uint8` and `Int8`, 2 for `Uint16` and `Int16`, 4 for `Uint32` and `Int32`, and 8 for `Uint64` and
`Int64`, and $\mathrm{bit\_width} = 8 \times \mathrm{byte\_width}$.

Given a shape $s$, we define $\mathrm{size}(s) = \prod_i s.\mathrm{dimensions}[i]$ and require that valid shapes satisfy
$\mathrm{size}(s) < 2^{64}$.

Given a tensor type $t$, we define $\mathrm{byte\_size}(t) = \mathrm{size}(t.\mathrm{shape}) \times \mathrm{byte\_width}(t.\mathrm{dtype})$ and require
that valid tensor types satisfy $\mathrm{byte\_size}(t) < 2^{64}$.

#### Graphcode Definition

Graphcode is the compact on-chain representation of a computation graph. It is deployed and stored as
ordinary contract code that starts with the magic bytes `0xef 0x7f`, and is evaluated by calling the
`evalGraph` endpoint described in [Precompile Interface](#precompile-interface).

Valid graphcode conforms to the following schema, written in FlatBuffers-like notation, and has no
trailing bytes.

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
`n_inputs + n_ops - 1`. Nodes 0 to `n_inputs - 1` are the graph's inputs, and node `n_inputs + i`
is `ops[i]`.

Each entry in `outputs` MUST be a node id below `n_inputs + n_ops`. An output may be a graph input, and the
same node may appear more than once in `outputs`.

#### Operation Definition

The `ops` list in a graph definition contains the operation nodes.
Each operation node consists of an opcode, a list of operation-specific parameters and a list of inputs whose
length MUST equal the arity of the operation. Each input is provided as a node id, and
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

Any other opcode is invalid. The parameters and arity of each opcode are defined below. `Scalar`'s
are in [Scalar Definition](#scalar-definition). In the comments, `X` is an operation's first input.

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
    axis: uint8;       // axis < rank(X)
    n_inputs: uint8;   // 2 <= n_inputs <= MAX_CONCAT_INPUTS
}

ARITY(Concat) = n_inputs
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
    axis: uint8;   // axis < rank(X)
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
functions (fns) operating on `MAX_SCALAR_REGISTERS` registers. Instead of having a fixed
arity and input list, a `Scalar` node stores its inputs in its parameters. Its "outer" input
list as an operation is empty, so `ARITY(Scalar) = 0`.

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

Any other function id is invalid. The parameters and arity of each function are as follows:

| Fn                                                         | `FN_PARAMETERS`              | `FN_ARITY` |
|------------------------------------------------------------|------------------------------|------------|
| `Add`, `Sub`, `Mul`, `Div`, `Lt`, `Le`, `Eq`, `Min`, `Max` | none                         | 2          |
| `Divc`                                                     | `divisor: uint64` (not 0)    | 1          |
| `Where`                                                    | none                         | 3          |
| `Saturate`                                                 | `dtype: Dtype`               | 1          |
| `QMul`, `QDiv`                                             | `frac_bits: uint8`           | 2          |
| `QExp`, `QInvSqrt`                                         | `frac_bits: uint8`           | 1          |
| `ISqrt`                                                    | none                         | 1          |

A `Scalar` node MUST also satisfy the following conditions:

- Each node id in `inputs` refers only to an earlier node, as an operation's inputs do.
- Each input broadcasts to `output_shape`. Tensor broadcasting follows NumPy's broadcasting rules.
- Every operand is a register below `MAX_SCALAR_REGISTERS` that holds a value at that point: an
  input, a constant, or the destination of an earlier function.
- Every destination is at least `n_inputs + n_constants` and below `MAX_SCALAR_REGISTERS`, so input
  and constant registers are never written. A destination may be one of the function's own operands.
- Every function's operands have a dtype combination listed for it in [Scalar Evaluation](#scalar-evaluation).
  Input and constant registers inherit their values' dtypes. Any other register has the dtype of the most
  recent result written to it.
- For `QMul`, `QDiv`, `QExp` and `QInvSqrt`, `frac_bits` MUST be at most $\mathrm{bit\_width}(T)$,
  where $T$ is the dtype of the function's operands.

The output of the `Scalar` node has shape `output_shape` and the dtype of the last function's result.

#### Memory

Each graph input, and the output of each operation other than a `Literal`, a `TensorRef` or a `Reshape`,
consumes an amount of arena memory equal to its tensor's byte size, rounded up to a multiple of
`ARENA_ALIGNMENT`. The sum of these rounded sizes MUST be at most `ARENA_SIZE`. Conceptually, execution
proceeds as if memory were never freed even if a tensor is no longer used, but implementations
are free to reuse memory internally.

A `Literal`'s elements stay in the graph's code, a `TensorRef`'s output is the tensor's elements in
the referenced account's code, and a `Reshape`'s output shares its input's element storage, so none of
them uses arena memory. A `Scalar` node's registers are not part of the arena. The "Allocates" line of
each operation in [Operation Evaluation](#operation-evaluation) says whether its output consumes memory.

### Deploying Graphcode

Graphcode is deployed as the code of an ordinary account, by a contract-creation transaction,
`CREATE` or `CREATE2`, subject to the usual code size limit and a TBD code deposit cost.

[EIP-3541](https://eips.ethereum.org/EIPS/eip-3541) makes contract creation fail when the code it
would deploy starts with the byte `0xef`. This MIP adds one exception: creation does not fail for
that reason when the code starts with `GRAPH_MAGIC`. Code that starts with `0xef` followed by any
other byte is still rejected. It is an open question whether creation should also fail when code
that starts with `GRAPH_MAGIC` is not valid graphcode (see [Open Questions](#open-questions)).

`0xef` is not a defined opcode, so a call that executes graphcode as EVM code fails at once.

`TensorRef` nodes and `CodeRef` inputs read a tensor's elements directly from an account's code,
given the account's address and the offset of the elements' first byte from the first byte of the
code. The elements are `byte_size(type)` bytes in row-major order, each little-endian, where `type` is
the `TensorRef` node's `type` or the `CodeRef` input's `ty`. The code holds no type or other marker
for them. The call fails if those bytes extend past the end of the code.

Because of EIP-3541, code that holds only tensor data cannot start with `0xef`. A deployer can put a
`0x00` (`STOP`) byte before the data, which also makes a call to the account stop at once.

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

Inputs are provided as `TensorInput` structs, which specify the tensor's type and its location (embedded
in calldata as a literal or fetched from another contract's code). The contents of `payload` depend on
the `location` tag:

| `location` | `payload`                                                                                            |
|------------|------------------------------------------------------------------------------------------------------|
| Literal    | the tensor's elements, as row-major, big-endian bytes                                             |
| CodeRef  | `abi.encode(address account, uint32 offset)`, see [Deploying Graphcode](#deploying-graphcode) |

If the length of a `Literal` payload does not match the byte size of its corresponding type `ty` or
a `CodeRef` payload is not encoded according to the above format, the call fails.

`evalGraph` returns the graph's outputs as `Tensor`s, in the order of its `outputs` list. A `Tensor`
struct contains the tensor's type followed by a byte array containing the tensor's elements encoded
in big-endian order, stored in row-major order.

The precompile MUST be invoked with a `CALL` that sends no value.
`STATICCALL`, `DELEGATECALL`, `CALLCODE`, and calls through an
[EIP-7702](https://eips.ethereum.org/EIPS/eip-7702) delegation to the precompile's address MUST fail,
as with the MIP-4 reserve balance introspection precompile.

### Precompile Evaluation

A call to `evalGraph(graph, inputs)` evaluates the graphcode stored as the code of the account `graph`:

1. The code of `graph` MUST be valid graphcode according to the conditions in [Graphcode](#graphcode).
2. `inputs` MUST have exactly `graph.n_inputs` elements. For each `i`, the type `inputs[i].ty`
   MUST be equal to `graph.inputs[i]`.
3. The specified result is the one obtained by evaluating the operation nodes in their listed order, each
   from the outputs of earlier nodes, as described in [Operation Evaluation](#operation-evaluation).
4. The call returns the values of the nodes in `graph.outputs`.

Evaluation reads no state other than the code of `graph` and of the accounts that `TensorRef` nodes
and `CodeRef` inputs name, and writes none. Implementations MAY evaluate ops and elements in any order,
and MAY fuse, split or compile them, provided the outputs are those this section defines.

#### Failure

A call to the graph evaluation precompile MUST fail if any failure condition in this specification
applies, even in a node whose output is unused. Implementations MAY check conditions before or
during evaluation, in any order, provided they preserve the specified success or failure outcome.

A failed call reverts and consumes all gas supplied to it. The revert data is the same for every
failure (see [Open Questions](#open-questions)) and does not identify the failure condition or
evaluation step that caused the call to revert.

#### Operation Evaluation

$\mathrm{wrap}_T(v)$ is the value of dtype $T$ that is congruent to the integer $v$ modulo
$2^{\mathrm{bit\_width}(T)}$. Sums and products below are of exact integers, and wrap only where
stated. $T$ stands for any dtype. "Allocates" says whether the operation's output consumes arena
memory (see [Memory](#memory)).

* `Literal`

`Literal<type, elements>()` is the tensor of type `type` whose elements are read in row-major order
from `elements`, each as `byte_width(type.dtype)` little-endian bytes.

Valid dtype combinations:

| Out          |
|--------------|
| `type.dtype` |

Valid shape combinations:

| Out          |
|--------------|
| `type.shape` |

Allocates: no.

* `TensorRef`

`TensorRef<type, address, offset>()` is the tensor of type `type` whose elements are read in row-major
order from the `byte_size(type)` bytes at `offset` in the code of `address`, each as
`byte_width(type.dtype)` little-endian bytes (see [Deploying Graphcode](#deploying-graphcode)). The
call fails if those bytes extend past the end of the code.

Valid dtype combinations:

| Out          |
|--------------|
| `type.dtype` |

Valid shape combinations:

| Out          |
|--------------|
| `type.shape` |

Allocates: no.

* `Reshape`

`Reshape<shape>(X)` has $X$'s elements, in the same row-major order, and the shape `shape`.

Valid dtype combinations:

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

`Transpose<axis0, axis1>(X)` swaps dimensions `axis0` and `axis1` of $X$: for each input element,
exchange the coordinates along `axis0` and `axis1` to obtain the corresponding output coordinates.
For a matrix and axes 0 and 1, $\mathrm{Out}[i, j] = X[j, i]$. If `axis0` equals
`axis1`, the output is $X$.

Valid dtype combinations:

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

`Concat<axis, n_inputs>(X_0, ..., X_{n-1})`, with $n$ = `n_inputs`, joins its inputs along `axis`,
in order.

Valid dtype combinations:

| Each $X_i$ | Out |
|------------|-----|
| `T`        | `T` |

Valid shape combinations:

| Each $X_i$          | Out                                |
|---------------------|------------------------------------|
| `[p..., a_i, q...]` | `[p..., a_0 + ... + a_{n-1}, q...]` |

where `p...`, the dimensions before `axis`, and `q...`, the dimensions after it, are the same for
every input, and $a_0 + \dots + a_{n-1} \le$ `MAX_DIM`.

Allocates: yes.

* `QMatMul`

`QMatMul<frac_bits, out_dtype>(X, Y)` multiplies $X$ by the transpose of $Y$ exactly, then shifts
each sum right by `frac_bits`, rounding toward negative infinity, and wraps it to `out_dtype`:

$$\mathrm{Out}[i, j] = \mathrm{wrap}_{\mathrm{out\_dtype}}\left( \left\lfloor \frac{1}{2^{\mathrm{frac\_bits}}} \sum_{l=0}^{k-1} X[i, l] \cdot Y[j, l] \right\rfloor \right)$$

Valid dtype combinations:

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
elements at the corresponding position and all preceding positions along `axis`, holding every other
coordinate fixed.

Valid dtype combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X   | Out |
|-----|-----|
| `s` | `s` |

Allocates: yes.

* `ArgMin` and `ArgMax`

`ArgMin<axis>(X)` takes the index along `axis` of the smallest of $X$'s elements along `axis`,
holding the other coordinates fixed: $\mathrm{Out}[p, 0, q]$ is the smallest $i$ such that
$X[p, i, q] \le X[p, j, q]$ for every $j$, where $p$ stands for the coordinates before `axis` and $q$
for the coordinates after it. `ArgMax<axis>(X)` is the same with $\ge$ in place of $\le$. So if the
smallest (or largest) element appears more than once, the first index is returned.

Valid dtype combinations:

| X   | Out      |
|-----|----------|
| `T` | `Uint16` |

Valid shape combinations:

| X                 | Out               |
|-------------------|-------------------|
| `[p..., a, q...]` | `[p..., 1, q...]` |

where `p...` are the dimensions before `axis`, and $a \ge 1$. Every index is below $a \le$ `MAX_DIM`,
so it fits in a `Uint16`.

Allocates: yes.

* `ReduceSum` and `ReduceMax`

`ReduceSum<axis>(X)` sums $X$ along `axis`: each output element is $\mathrm{wrap}_T$ of the sum of
$X$'s elements along `axis`, holding the other coordinates fixed. `ReduceMax<axis>(X)` returns the maximum
over the same elements.

Valid dtype combinations:

| X   | Out |
|-----|-----|
| `T` | `T` |

Valid shape combinations:

| X                 | Out               |
|-------------------|-------------------|
| `[p..., a, q...]` | `[p..., 1, q...]` |

where `p...` are the dimensions before `axis`, and $a \ge 1$.

Allocates: yes.

* `Gather`

`Gather<axis>(X, I)` takes elements of $X$ along `axis` at the positions given by $I$:
$\mathrm{Out}[p, r, q] = X[p, I[r], q]$, where $p$ stands for the coordinates before `axis`, $r$ for
$I$'s coordinates and $q$ for the coordinates after `axis`. The call fails if any element of $I$ is
negative or at least $a$.

Valid dtype combinations:

| X   | I               | Out |
|-----|-----------------|-----|
| `T` | any dtype       | `T` |

Valid shape combinations:

| X                 | I      | Out                  |
|-------------------|--------|----------------------|
| `[p..., a, q...]` | `[r...]` | `[p..., r..., q...]` |

where `p...` are the dimensions before `axis`, and the output's rank is at most `MAX_RANK`.

Allocates: yes.

* `Scalar`

See [Scalar Evaluation](#scalar-evaluation).

Allocates: yes.

#### Scalar Evaluation

A `Scalar` node computes each element of its output independently:

1. Each input register holds the input's element that corresponds to the output element,
   after broadcasting the input tensor to the `Scalar` node's output shape.
2. Each constant register holds its constant.
3. The functions are executed in their listed order. Each reads all its operands before producing a
   result. Every function except the last writes its result to its destination register; the last function
   produces the output element.

In the table below, $a$, $b$ and $c$ are the function's operands, $T$
is a metavariable that stands for an arbitrary dtype, and $f$ is the
function's `frac_bits` parameter (when it applies).

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
| `Where`    | `Uint8`, `T`, `T` | `T`      | $b$ if $a \ne 0$, else $c$                                                             |
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
    for n = 19 down to 0:          // p approximates exp(s / 2^63), with 63 fractional bits
        p = C[n] + floor(p * s / 2^63)
    return min(floor(p * 2^(k + f - 63)), max_T)   // max_T is T's maximum
```

A normative reference implementation will be provided in the assets of this MIP.

### Gas Costs

The gas schedule is not yet set, but we outline a general structure here.

- A fixed base cost per call.
- Reading call inputs passed as `CodeRef`, priced as MIP-20 code loads.
- Per-operation gas costs computed as a function of the input shapes and dtypes, with each operation
  defining its own cost function.
  - A `Scalar` node costs a flat amount, an extra amount for any input that needs broadcasting,
    and a per-function cost paid for each output element, for a total of
    $$G_{opcode} + G_{inputbroadcasting} + (\sum_i G_{fns[i]}) \times \mathrm{size}(\texttt{output\_shape})$$
    An efficient pricing scheme will likely need fractional gas costs for cheap functions.
  - A `TensorRef` node is priced as a MIP-20 code load.
- Arena memory, per byte of the graph's allocated memory size (see [Memory](#memory)).

Apart from code-loading charges (which may change, for example if new contracts are deployed at the addresses
referenced by a graph's `TensorRef` nodes), all costs depend only on the graphcode and can be computed
and cached in advance.
A call whose gas does not cover the cost fails.

## Rationale

### The magic bytes

Graphcode's header follows the one that
[EIP-3540](https://eips.ethereum.org/EIPS/eip-3540) proposes for EVM Object Format (EOF) contracts:
two magic bytes starting with `0xef`, then a version byte. EOF's magic is `0xef 0x00`, and
graphcode's is `0xef 0x7f`. As in EIP-3540, the first version is 1.
[EIP-3541](https://eips.ethereum.org/EIPS/eip-3541) reserved code starting with `0xef` for such
formats, and [EIP-7702](https://eips.ethereum.org/EIPS/eip-7702)'s delegation indicator `0xef0100`
also uses that prefix. Because of EIP-3541, no account on Monad has code starting with `0xef 0x7f`,
so no existing contract can be mistaken for graphcode, and graphcode run as EVM code fails at once.

### Tensors in any account's code

Referenced tensors have no type or marker of their own in code: a `TensorRef` node or `CodeRef` input
names any byte range of any account's code, and its type comes from the node or the input. A graph
can therefore read another graph's `Literal` elements, part of a larger tensor (for example one row of
a matrix), or data written by any tool, and weights larger than the code size limit can be split
across several accounts. Because every node's type is in the graph's own code, a graph's validity,
node types and memory layout do not depend on other accounts' code. The precompile has no way to
check that the bytes hold the tensor the graph expects: a wrong address or offset reads other bytes
as elements.

### Integer dtypes of at most 64 bits

Integer arithmetic with defined rounding ensures identical results on every implementation and
machine, which is significantly harder to achieve with floating point. The fixed-point functions
(`QMul`, `QDiv`, `QExp`, `QInvSqrt`) and `QMatMul` state their rounding exactly. Narrow dtypes contribute
to the speedup over EVM code. On an AMD Zen 4 CPU, a chain of dependent 16.16 multiplications on one
`int32` costs 4.9 ns per multiplication in the reference implementation's interpreter (3.2 ns with an
experimental path for single-element `Scalar` nodes), against 6.2 ns for the same chain in compiled EVM code and
31.7 ns in interpreted EVM code.

### One matrix multiplication, with its second operand transposed

`QMatMul` with `frac_bits == 0` is an exact integer matrix product, wrapped to `out_dtype`, so a separate
`MatMul` is not needed: with `Int8` inputs and an `Int32` output, sums cannot overflow, since each sum is
at most $65535 \cdot 2^{14} < 2^{31}$ in magnitude. Multiplying by the transpose $Y^T$ makes every output
element the dot product of two rows, both contiguous in memory, and matches the layout in which PyTorch
stores a linear layer's weights (output features by input features).

### Static shapes and a bounded, never-reused arena

Static shapes let implementations determine every tensor's type, the arena layout and most
evaluation costs from the graphcode before a call. They are then free to use this information to
optimize evaluation.

Because memory is never reused, graphcode authors can calculate arena usage by summing up the rounded
sizes of all graph inputs and the outputs that allocate arena memory. Implementations are free to
reuse freed memory internally, for example to improve cache locality, but this is not exposed to the user
as it would make changes to the allocator visible at the consensus level.

### Scalar nodes

Elementwise arithmetic is common and easy to optimize; an implementation may, for example, choose to
compile long chains of elementwise operations ahead of time into compact blocks of SIMD
instructions. Elementwise operations can be evaluated one block at a time without storing
intermediate tensors, which reduces memory use. Grouping chains of elementwise operations into
`Scalar` nodes has two purposes:
* It reduces memory use in many common graphs: an implementation can evaluate a node's elements in
  blocks without storing intermediate results, and needs no analysis pass to find which operations
  can be combined.
* It makes nodes easier to compile. The register count (14) and the 64-bit limit on dtypes mean that
  all of a node's registers fit in x86-64's 16 general-purpose registers at once. A node with
  single-element tensors can be compiled by emitting a fixed instruction sequence per function, with
  each node register held in its own machine register, so the compiler needs no register
  allocation. A prototype
  template compiler built this way on asmjit took about 0.5 µs per node plus 9 to 11 ns per
  instruction emitted.

### No storage access

Graphcode has no storage-access operations. A contract that keeps tensors in storage must read
them with `SLOAD` and pass them as literal inputs, and then store the outputs with `SSTORE`.

An earlier draft also let a call pass inputs and outputs by reference to the caller's storage. That
design would let storage accesses be priced more cheaply. A contract pays at least a base cost
for every slot it reads or writes, even when reading multiple slots in the same page under MIP-8.
A precompile that knows all the slots a call will read or write in advance could instead charge for access
once per page, without extending the EVM with page-level storage operations. This approach was left out
to minimize complexity but can be added later as a new endpoint, with no change to graphcode.

### A single failure outcome

Because every failure looks the same, implementations can reorder, fuse, split and compile
evaluation freely, and can check validity ahead of time or during evaluation. This matches the EVM,
where exceptional halts are not distinguished.

## Backwards Compatibility

This MIP uses a new precompile address, `0x1002`, which had no code. Calls to it that used to
succeed as calls to an empty account now evaluate a graph, and fail unless their calldata is a valid
`evalGraph` call.

Before this MIP, [EIP-3541](https://eips.ethereum.org/EIPS/eip-3541) made deploying any code starting
with `0xef` fail. Since `0xef 0x7f` is now a valid contract header, deploying such a contract no
longer fails because of EIP-3541.

## Security Considerations

### Bounded work

The cost of validation is linear in the length of the graph's code. The
code deposit cost for graphcode should be chosen so that repeatedly deploying
large graphs cannot be used for a denial-of-service attack.

Graphs have no control flow operators and no way to make calls, so execution time is always bounded.
The amount of memory a call uses is also bounded by `ARENA_SIZE`, plus the code of the
accounts the call references (which are in turn limited by MIP-20 gas costs).

### Pricing must cover the worst case

An operation's running time is not a fixed amount per element or per multiply-add. For example,
`QMatMul` of an `[m, k]` tensor $X$ and an `[n, k]` tensor $Y$ performs $m \cdot n \cdot k$
multiply-adds, but shapes with the same product can take very different times:

- Each of the $m \cdot n$ output elements has a fixed cost, for starting its sum and for shifting,
  wrapping and storing it. With $m = n = 1000$ and $k = 1$ this cost is paid $10^6$ times, and with
  $m = n = 10$ and $k = 10^4$ it is paid 100 times, for the same $10^6$ multiply-adds.
- An implementation that computes each dot product in SIMD blocks of $B$ elements handles the
  $k \bmod B$ elements left over separately, often one at a time. With $B = 32$, $k = 63$ leaves 31
  of each dot product's 63 multiply-adds to the slower path, but $k = 64$ does not.
- An implementation that reads all of $Y$ for each row of $X$ finds $Y$ in the CPU's caches after
  the first row if $Y$ fits in them, and may need to reload it from main memory for every row if it does not.
  Whether it fits depends on $n \cdot k$ and the dtype, not on $m \cdot n \cdot k$.

A price per multiply-add measured on one shape would undercharge others. `QMatMul`'s cost function
needs terms other than $m \cdot n \cdot k$, for example one per output element, and every operation's
constants must be set from measurements of the slowest shapes and dtypes a graph can use, such as a
$k$ just below a multiple of the block length or a $Y$ larger than the caches.

Other operations are also sensitive to cache misses. The arena can be larger than a CPU's caches,
`TensorRef` nodes and `CodeRef` inputs read code that may not be in any cache, and `Gather` reads
elements at positions that are chosen by the operation's inputs. An operation's latency can depend
on where its inputs are stored, and an adversarial graph can force cache misses, so that a
call takes longer than its gas pays for. Prices should be set from measurements with cold caches and tensors as
large as the arena allows.

### Consensus

Every result is defined exactly over each dtype's whole range. An implementation that diverges on
any input can cause a consensus split, so implementations should be tested differentially against each other
and the reference algorithms, over every operation, function and dtype.

### References

`TensorRef` nodes and `CodeRef` inputs can name any account. Their reads are priced
as code loads. The precompile writes no state, so no call changes storage,
whether it fails or not.

A `TensorRef`'s output takes no arena memory, so `ARENA_SIZE` does not limit how much referenced
data a call reads: multiple `TensorRef` nodes can reference large tensors for the price of one code load
each. Implementations should read referenced tensors in place, in the account's code, as they
read `Literal` elements. An implementation that copies them uses memory that the arena does not
account for, up to `MAX_GRAPH_OPS` times the code size limit in one call.

## Open Questions

- **Operation list:** the list of operations and functions here is a
  work in progress, chosen to cover a set of example workloads.
- **Gas cost numbers:** gas costs should be set from worst-case
  measurements of the supported operations and dtypes.
- **Validation at deployment:** whether deploying code that starts
  with `0xef 0x7f` but is not a valid graph should fail.
- **Revert data on failure:** whether to leave it empty or provide
  minimal error information (without preventing implementations from
  detecting failures in any order).

## Copyright

Copyright and related rights waived via CC0.
