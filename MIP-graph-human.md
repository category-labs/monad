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
on signed and unsigned integer types most 64 bits wide, with no
support for control flow, side-effects, floating point or dynamic
shapes. Callers pass the graph's inputs by value, by reference to
another account's code or by reference to the caller's storage, and
receive the outputs back or have them written to the caller's storage.

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
**CLAUDE: Let's see if we can find a neural network example with gas**

A precompile that takes a whole computation as one graph of tensor
operations can execute it with machine-width integer arithmetic,
without per-element dispatch. Because the graph is fixed in advance,
its validity, memory use and most of its cost are known before it
runs, which opens the door to efficient compilation.

## Specification

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT", "SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and "OPTIONAL" in this document are to be interpreted as described in [RFC 2119](https://www.ietf.org/rfc/rfc2119.html) and [RFC 8174](https://www.ietf.org/rfc/rfc8174.html).

### Constants

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

### Graphcode

#### Tensors, Shapes and Types

Like in most tensor computing frameworks, a tensor has a _type_ which consists
of a _shape_ (a list of dimension sizes) and a _dtype_ (the type of its
elements).

Tensor types conform to the following schema, written in FlatBuffers-like format.

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
    rank: u8;                // 0 <= rank <= MAX_RANK
    dimensions: [u16:rank];  // 0 <= dimensions[i] <= MAX_DIM
}

struct Type {
    shape: Shape;
    dtype: Dtype;
}
```

Given a shape $s$, we define $size(s) = \Product_i(s.dimensions[i])$ and require that valid shapes verify
$size(s) < 2^64$.

Given a tensor type $t$, we define $byte_size(t) = size(t.shape) \times byte_width(t.dtype)$ and require
that valid tensor types verify $byte_size(s) < 2^64$.

#### Graphcode Definition

Graphcode is the compact on-chain representation of a computation graph. It is deployed and stored as
regular contract code that starts with the magic bytes
`0xfe 0x7f` and invoked indirectly via a call to the `evalGraph` endpoint described in &&REFERENCE&&.

Valid graphcode conforms to the following schema, written in FlatBuffers-like format and without trailing bytes.

```
struct NodeId {
    value: uint16;
}

struct Graph {
    magic_number: uint8;         // magic_number == MAX_RANK
    version: uint8;              // version == 0
    n_inputs: uint8;             // 0 <= n_inputs <= MAX_GRAPH_INPUTS
    inputs: [Type:n_inputs];
    n_outputs: uint8;            // 0 <= n_outputs <= MAX_GRAPH_OUTPUTS
    outputs: [NodeId:n_outputs];
    n_ops: uint16;               // 0 <= n_ops <= MAX_GRAPH_OPS
    ops: [Op:n_ops];
}
```

Graphcode encodes a computation graph as a list of topologically-ordered nodes, numbered from 0 to N.
Nodes 0 to `n_inputs` are the graph's inputs, with node `n_inputs+1` corresponding to `ops[0]`, `n_inputs+2`
corresponding to `ops[1]` and so forth.


#### Operation Definition

The `ops` list in a graph definition consists of a list of operation nodes.
Each operation node consists of an opcode, a list of operation-specific parameters and a list of inputs which
must match the arity of the operation. Each input is provided as an index into the graph's `ops` list, and
must refer only to previous nodes (either inputs or operations). That is, the inputs of `ops[i]` must
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
    Transpose
    Concat,
    QMatMul,
    CumSum,
    ArgMin,
    ArgMax,
    ReduceMin,
    ReduceMax,
    Gather,
}
```

The parameters and arity of each opcode are as described below, with the exception of `Scalar` nodes which
are described with more depth in their own section &&REFERENCE&&.

* `QMatMul`

```
struct PARAMETERS(QMatMul) {
    frac_bits: uint8; // 0 <= frac_bits <= bit_width(out_dtype)
    out_dtype: Dtype;
}

ARITY(QMatMul) = 2
```

#### Scalar Validation

### Deploying Graphcode

### Precompile Interface

**CLAUDE: We're not including evalGraphInto.**

### Precompile Evaluation

#### Operation Evaluation

* `QMatMul`

**CLAUDE: see if you can find a nicer way to layout this semantics**
`QMatMul<frac_bits, out_dtype>(X, Y)` performs exact matrix multiplication of $X$ by
the transpose $Y^T$, with a post-accumulation shift and wrap to `dtype`. Formally,
if $P$ is the exact matrix product $P = X Y^T$ then $QMM[i, j] = low bit_width(out_dtype) bits of (P >> frac_bits)`.

Valid type combinations:

| X        | Y        | Out          |
|----------|----------|--------------|
| `uint8 ` | `uint8 ` | `out_dtype`  |
| `int8  ` | `int8  ` | `out_dtype ` |
| `uint16` | `uint16` | `out_dtype`  |
| `int16 ` | `int16 ` | `out_dtype ` |
| `uint32` | `uint32` | `out_dtype`  |
| `int32 ` | `int32 ` | `out_dtype ` |
| `uint64` | `uint64` | `out_dtype`  |
| `int64 ` | `int64 ` | `out_dtype ` |

Valid shape combinations:

| X      | Y      | Out    |
|--------|--------|--------|
| [i, j] | [k, j] | [i, k] |

Allocates: yes.

#### Scalar Evaluation

### Gas Costs

## Rationale

## Backwards Compatibility

**CLAUDE: mention that we take up a new precompile slot.**

**CLAUDE: since 0xef 0x7f is now a valid contract header, deploying such a contract no longer fails.**

## Security Considerations

### Bounded work

The cost of validation is linear in the length of the graph's code. The
code-deposit cost for graphcode should be chosen so that repeatedly deploying
large graphs is not a DoS opportunity.

Graphs have no control flow operators and no means of performing calls, so
execution time is always bounded. Memory usage within each call is also bounded
by `ARENA_SIZE`.

### Pricing must cover the worst case

**CLAUDE: bad example, since Scalar no longer has the concept of a "broadcast run"**
An operation's cost can fluctuate depending on its layout as well as its element
count. In the reference implementation, the same `int32` `QMul` over 13,520
elements took 8.54 µs or 1.71 µs depending on whether its broadcast runs were 10
or 1352 elements long. Prices set from long runs would undercharge short ones.
Prices must also assume the slowest path an attacker can force.

**CLAUDE: maybe add something about cache effects potentially mattering?**

### Consensus

Every result is defined exactly over each dtype's whole range. An
implementation that diverges on any input splits the network, so implementations
should be tested differentially against each other and the reference algorithms,
over every op, fn and dtype.

### References

`TensorRef` nodes and code inputs can name any account. Their reads are priced
as code loads. Storage writes happen only under `DELEGATECALL`, only to the
caller's own storage, never in a static context, and only after the whole
graph has been evaluated, so a failed call does not touch storage.

## Open Questions

- **Operation list:** the list of operations and functions provided
  here is a WIP and was selected to cover a number of illustrative
  examples.
- **Gas cost numbers:** gas costs should be picked based on
  conservative estimates of realistic workloads.
- **Validation at deployment:** whether deploying code that starts
  with `fe 7f` but is not a valid graph should fail.
- **Revert data on failure:** whether to leave it empty or provide
  minimal error information (without compromising implementations')
