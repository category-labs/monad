#!/usr/bin/env python3
"""Encodes a graph for the graph eval precompile as graphcode.

Graphs are written in a short text form, which this reads. Opcodes, dtype ids,
the magic number and limits are read from the C++ sources rather than copied,
so they can't drift.

One statement per line. `#` starts a comment, and a statement with unclosed
brackets, or ending in a comma, continues onto the next line.

    input x: int8[2, 3]             a graph input; int8[] is a scalar
    y = add(x, x)                   an op, whose result is the node y
    output y, x                     the graph's outputs, in order
    call example                    values for the graph's inputs, which
                                    monad-bench runs it on, one per input:
        x = [[1, 2, 3], [4, 5, 6]]  a nested list of the input's shape, or an
                                    integer for a scalar, of its dtype
    data 0xda7a: int8[2] [1, 2], int64[] 7
                                    an account whose code holds tensors, for
                                    tensorref: a 0x00 byte, then each tensor
                                    encoded as a literal is, one after another;
                                    here the first is at offset 1 and the
                                    second at offset 7
    data 0xda7b: 0x00ff             an account with exactly this code

Ops, whose arguments are nodes unless noted; ops.hpp has the details. add, sub,
mul, qmul, qdiv, max, min, greater, ge, equal and where broadcast their
operands' shapes together as numpy does. The q ops read their operands as fixed
point, with the number of fractional bits given, at most 63.

    literal(int8[2] [1, 2])         a constant
    tensorref(int8[2], 0xda7a, 1)   the tensor at a byte offset in an account's
                                    code, counted from the code's start, as a
                                    data statement puts it there; fails unless
                                    the code starts with 0x00 and a tensor of
                                    the type given is at the offset
    add(a, b)  sub(a, b)            same dtype; wraps on overflow
    mul(a, b)                       same dtype; the product in the type twice as
                                    wide, or wrapping for 64-bit types
    max(a, b)  min(a, b)            same dtype
    greater(a, b)  ge(a, b)  equal(a, b)
                                    same dtype; uint8 0 or 1
    where(condition, a, b)          uint8 condition; a and b the same dtype
    div(a, 16)                      a nonzero int64 denominator; truncates
                                    toward zero, and wraps on overflow
    matmul(a, b)                    int8 matrices; an int32 product
    argmax(a)                       the row-major index of the first largest
                                    element, a scalar of a's dtype
    reshape(a, [3, 2])              a shape with the same element count
    saturate(a, uint8)              a dtype to convert to, clamping
    expand(a, [4, 2, 3])            a shape to broadcast to, as
                                    numpy.broadcast_to does
    cumsum(a, 0)                    an axis to sum along; wraps on overflow
    reducesum(a, 1)  reducemax(a, 1)
                                    an axis to reduce, which stays, with length
                                    1; reducesum wraps on overflow, and is 0
                                    along an empty axis, where reducemax fails
    qmul(a, b, 48)                  same dtype; a * b / 2^48, rounding down and
                                    wrapping on overflow
    qdiv(a, b, 48)                  same dtype; a * 2^48 / b, truncating toward
                                    zero and wrapping; fails if b has a zero
    qmatmul(a, b, 48, int64)        matrices of the same dtype; each element's
                                    products summed, wrapping at 128 bits, then
                                    divided by 2^48, rounding down, and wrapped
                                    to the dtype given
    qexp(a, 48)  qinvsqrt(a, 48)    e^a and 1/sqrt(a), rounding down and
                                    saturating; qinvsqrt fails if a has an
                                    element that isn't positive
    gather(a, indices, 0)           the slices of a along an axis at each of
                                    indices, of any dtype, as numpy.take does;
                                    fails if an index isn't in [0, length)
    concat(a, b, 0)                 a and b joined along an axis; same dtype and
                                    rank, and the same dimensions but that one

Usage:
    ./graphcode.py example.graph [-o example.hex]
    ./graphcode.py --from-json mnist.json [-o mnist.graph]

The first form prints the graph's graphcode in hex. The second converts a graph
in the JSON form of mnist.json, with op names as in graph.hpp, to this format
instead, naming node i t{i}.
"""

import argparse
import ast
import json
import re
import struct
from collections import namedtuple
from pathlib import Path

# This script is in the repository's scripts/
REPO_ROOT = Path(__file__).resolve().parent.parent
GRAPH_EVAL_DIR = REPO_ROOT / "category/execution/monad/graph_eval"
MAX_RANK = 8
MAX_DIMENSION = 0xFFFF
MAX_NODES = 0xFFFF

#
# Definitions read from the C++ sources
#


def _find(pattern, file_name):
    source = (GRAPH_EVAL_DIR / file_name).read_text()
    match = re.search(pattern, source, re.S)
    if not match:
        raise RuntimeError(
            f"no match for {pattern!r} in {file_name}; graphcode.py needs "
            "updating")
    return match


def _enum(name, file_name):
    """Enumerator -> value for `enum class name`, aliases included"""
    body = _find(r"enum class " + name + r"\b[^{]*\{(.*?)\}", file_name)[1]
    body = re.sub(r"//[^\n]*", "", body)
    values, next_value = {}, 0
    for entry in filter(None, (e.strip() for e in body.split(","))):
        key, _, value = (s.strip() for s in entry.partition("="))
        if value:
            next_value = values[value] if value in values else int(value, 0)
        values[key] = next_value
        next_value += 1
    return values


OP_IDS = _enum("Op", "graph.hpp")
MAGIC = int(_find(r"GRAPH_MAGIC = (0x[0-9a-fA-F]+)", "constants.hpp")[1], 16)
MAX_GRAPH_INPUTS = int(_find(r"MAX_GRAPH_INPUTS = (\d+)", "constants.hpp")[1])
MAX_GRAPH_OUTPUTS = int(
    _find(r"MAX_GRAPH_OUTPUTS = (\d+)", "constants.hpp")[1])


class Dtype(namedtuple("Dtype", "name id size signed")):
    @property
    def min(self):
        return -(1 << (8 * self.size - 1)) if self.signed else 0

    @property
    def max(self):
        return (1 << (8 * self.size - self.signed)) - 1

    def encode(self, values, byteorder):
        return b"".join(v.to_bytes(self.size, byteorder, signed=self.signed)
                        for v in values)


DTYPES = {}
for _name, _id in _enum("Dtype", "types.hpp").items():
    if _match := re.fullmatch(r"(u?)int(8|16|32|64)", _name):
        DTYPES[_name] = Dtype(_name, _id, int(_match[2]) // 8, not _match[1])

#
# Parser
#

# Row-major values as Python ints, and dims as a tuple
Tensor = namedtuple("Tensor", "dtype dims values")

# DSL name -> (Op enumerator, argument kinds). Parameters, the arguments that
# aren't nodes, are encoded before the input node ids, as the interpreter reads
# them
OPS = {
    "literal": ("Literal", ["tensor"]),
    "tensorref": ("TensorRef", ["type", "address", "offset"]),
    "add": ("Add", ["node", "node"]),
    "sub": ("Sub", ["node", "node"]),
    "mul": ("Mul", ["node", "node"]),
    "max": ("Max", ["node", "node"]),
    "min": ("Min", ["node", "node"]),
    "greater": ("Greater", ["node", "node"]),
    "ge": ("Ge", ["node", "node"]),
    "equal": ("Equal", ["node", "node"]),
    "where": ("Where", ["node", "node", "node"]),
    "reshape": ("Reshape", ["node", "shape"]),
    "saturate": ("Saturate", ["node", "dtype"]),
    "expand": ("Expand", ["node", "shape"]),
    "cumsum": ("CumSum", ["node", "axis"]),
    "div": ("Div", ["node", "int64"]),
    "matmul": ("MatMul", ["node", "node"]),
    "argmax": ("ArgMax", ["node"]),
    "reducesum": ("ReduceSum", ["node", "axis"]),
    "reducemax": ("ReduceMax", ["node", "axis"]),
    "qmul": ("QMul", ["node", "node", "bits"]),
    "qdiv": ("QDiv", ["node", "node", "bits"]),
    "qmatmul": ("QMatMul", ["node", "node", "bits", "dtype"]),
    "qexp": ("QExp", ["node", "bits"]),
    "qinvsqrt": ("QInvSqrt", ["node", "bits"]),
    "gather": ("Gather", ["node", "node", "axis"]),
    "concat": ("Concat", ["node", "node", "axis"]),
}


class DslError(Exception):
    def __init__(self, line, message):
        super().__init__(f"line {line}: {message}")


# An op's result. `params` are its non-node arguments and `inputs` the node ids
# of the rest, each in argument order
Node = namedtuple("Node", "op params inputs")


class Call:
    def __init__(self, label):
        self.label = label
        self.inputs = {}  # input name -> Tensor


class Graph:
    def __init__(self):
        self.inputs = []  # (name, dtype, dims)
        self.nodes = []
        self.outputs = None  # node ids
        self.ids = {}  # name -> node id, the graph inputs' first
        self.calls = []  # Calls
        self.accounts = {}  # address -> code, from the data statements


def _statements(text):
    """(line number, statement) pairs, without comments, joining a statement
    that has unclosed brackets with the lines that follow"""
    pending, start = "", 0
    for number, line in enumerate(text.splitlines(), 1):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if not pending:
            start = number
        pending = f"{pending} {line}".strip()
        depth = (sum(map(pending.count, "([")) -
                 sum(map(pending.count, ")]")))
        if depth < 0:
            raise DslError(number, "unbalanced brackets")
        if depth == 0 and not pending.endswith(","):
            yield start, pending
            pending = ""
    if pending:
        raise DslError(start, "unclosed bracket")


def _split_args(text):
    """Splits on the commas that aren't inside brackets"""
    args, depth, start = [], 0, 0
    for i, c in enumerate(text):
        depth += (c in "([") - (c in ")]")
        if c == "," and depth == 0:
            args.append(text[start:i].strip())
            start = i + 1
    args.append(text[start:].strip())
    return [] if args == [""] else args


def _check_dims(dims, line):
    if len(dims) > MAX_RANK:
        raise DslError(line, f"rank {len(dims)} is more than {MAX_RANK}")
    if not all(0 <= d <= MAX_DIMENSION for d in dims):
        raise DslError(line, f"dimensions must be in [0, {MAX_DIMENSION}]")
    return tuple(dims)


def _parse_dims(text, line):
    try:
        dims = ast.literal_eval(text)
    except (ValueError, SyntaxError):
        dims = None
    if not isinstance(dims, list) or not all(type(d) is int for d in dims):
        raise DslError(line, f"expected a shape like [2, 3], not {text!r}")
    return _check_dims(dims, line)


_TYPE = re.compile(r"(\w+)\s*\[([^\]]*)\]")


def _parse_type(text, line):
    match = _TYPE.fullmatch(text.strip())
    if not match or match[1] not in DTYPES:
        raise DslError(line, f"expected a type like int8[2, 3], not {text!r}")
    return DTYPES[match[1]], _parse_dims(f"[{match[2]}]", line)


def _flatten(value, dims, line):
    if not dims:
        if type(value) is not int:
            raise DslError(line, f"expected an integer, not {value!r}")
        return [value]
    if not isinstance(value, list) or len(value) != dims[0]:
        raise DslError(line, f"{value!r} doesn't have shape {list(dims)}")
    return [v for item in value for v in _flatten(item, dims[1:], line)]


def _parse_value(text, line, dtype=None):
    """A tensor from a nested list of integers, or a single integer for a
    scalar, preceded by its type. Without the type, the dtype is `dtype` and
    the shape is the nesting's."""
    match = _TYPE.match(text)
    if match and match[1] in DTYPES:
        dtype, dims = _parse_type(match[0], line)
        text = text[match.end():]
    elif dtype is None:
        raise DslError(line, "expected a type before the value, as in "
                       "int8[2] [1, 2]")
    else:
        dims = None
    try:
        value = ast.literal_eval(text.strip())
    except (ValueError, SyntaxError):
        raise DslError(line, f"invalid value {text.strip()!r}") from None
    if dims is None:
        dims, nested = [], value
        while isinstance(nested, list):
            dims.append(len(nested))
            nested = nested[0] if nested else None
        dims = _check_dims(dims, line)
    values = _flatten(value, dims, line)
    if not all(dtype.min <= v <= dtype.max for v in values):
        raise DslError(line, f"values must be in [{dtype.min}, {dtype.max}] "
                       f"for {dtype.name}")
    return Tensor(dtype, dims, values)


def _parse_address(text, line):
    if not re.fullmatch(r"0x[0-9a-fA-F]{1,40}", text):
        raise DslError(line, f"expected an address like 0xda7a, not {text!r}")
    return int(text, 16).to_bytes(20, "big")


def _define(graph, line, name):
    if name in graph.ids:
        raise DslError(line, f"{name} is already defined")
    graph.ids[name] = len(graph.ids)


def _node_id(graph, line, name):
    if name not in graph.ids:
        raise DslError(line, f"unknown node {name!r}")
    return graph.ids[name]


def _parse_op(graph, line, name, op, args_text):
    if op not in OPS:
        raise DslError(line, f"unknown op {op!r}")
    kinds = OPS[op][1]
    args = _split_args(args_text)
    if len(args) != len(kinds):
        raise DslError(line, f"{op} takes {len(kinds)} arguments")
    params, inputs = [], []
    for kind, arg in zip(kinds, args):
        if kind == "node":
            inputs.append(_node_id(graph, line, arg))
        elif kind == "shape":
            params.append(_parse_dims(arg, line))
        elif kind == "dtype":
            if arg not in DTYPES:
                raise DslError(line, f"unknown dtype {arg!r}")
            params.append(DTYPES[arg])
        elif kind == "axis":
            if not re.fullmatch(r"\d+", arg) or int(arg) > 0xFF:
                raise DslError(line, f"expected an axis in [0, 255], not "
                               f"{arg!r}")
            params.append(int(arg))
        elif kind == "bits":
            if not re.fullmatch(r"\d+", arg) or int(arg) > 0xFF:
                raise DslError(line, f"expected a number of fractional bits "
                               f"in [0, 255], not {arg!r}")
            params.append(int(arg))
        elif kind == "int64":
            if not re.fullmatch(r"-?\d+", arg) or not (
                    -(1 << 63) <= int(arg) < 1 << 63):
                raise DslError(line, f"expected an int64, not {arg!r}")
            params.append(int(arg))
        elif kind == "type":
            params.append(_parse_type(arg, line))
        elif kind == "address":
            params.append(_parse_address(arg, line))
        elif kind == "offset":
            if not re.fullmatch(r"\d+", arg) or int(arg) > 0xFFFFFFFF:
                raise DslError(line, f"expected an offset in [0, 2^32), not "
                               f"{arg!r}")
            params.append(int(arg))
        else:
            params.append(_parse_value(arg, line))
    _define(graph, line, name)
    graph.nodes.append(Node(op, params, inputs))


def parse(text):
    graph = Graph()
    call = None
    line = 0
    for line, statement in _statements(text):
        if match := re.fullmatch(r"(\w+)\s*=\s*(.+)", statement):
            name, rhs = match[1], match[2]
            if call is not None:
                input_types = {n: (dtype, dims)
                               for n, dtype, dims in graph.inputs}
                if name not in input_types:
                    raise DslError(line, f"{name} isn't a graph input")
                if name in call.inputs:
                    raise DslError(line, f"{name} is already given")
                dtype, dims = input_types[name]
                tensor = _parse_value(rhs, line, dtype)
                if (tensor.dtype, tensor.dims) != (dtype, dims):
                    raise DslError(
                        line, f"{name} is {dtype.name}{list(dims)}, not "
                        f"{tensor.dtype.name}{list(tensor.dims)}")
                call.inputs[name] = tensor
            elif op := re.fullmatch(r"(\w+)\s*\((.*)\)", rhs):
                if graph.outputs is not None:
                    raise DslError(line, "ops must come before the outputs")
                _parse_op(graph, line, name, op[1], op[2])
            else:
                raise DslError(line, f"expected an op call, not {rhs!r}")
        elif match := re.fullmatch(r"input\s+(\w+)\s*:\s*(.+)", statement):
            if graph.nodes or graph.outputs is not None or call is not None:
                raise DslError(line, "inputs must come before everything else")
            _define(graph, line, match[1])
            graph.inputs.append((match[1], *_parse_type(match[2], line)))
        elif match := re.fullmatch(r"output\s+(.+)", statement):
            if graph.outputs is not None or call is not None:
                raise DslError(line, "there must be one output statement, "
                               "before the calls")
            graph.outputs = [_node_id(graph, line, n.strip())
                             for n in match[1].split(",")]
        elif match := re.fullmatch(r"call\s+(\w+)", statement):
            if graph.outputs is None:
                raise DslError(line, "calls must come after the outputs")
            if any(c.label == match[1] for c in graph.calls):
                raise DslError(line, f"call {match[1]} is already defined")
            call = Call(match[1])
            graph.calls.append(call)
        elif match := re.fullmatch(r"data\s+(\w+)\s*:\s*(.+)", statement):
            address = _parse_address(match[1], line)
            if address in graph.accounts:
                raise DslError(line, f"{match[1]} already has data")
            if re.fullmatch(r"0x([0-9a-fA-F]{2})*", match[2]):
                graph.accounts[address] = bytes.fromhex(match[2][2:])
            else:
                graph.accounts[address] = data_code(*(
                    _parse_value(arg, line) for arg in _split_args(match[2])))
        else:
            raise DslError(line, f"unrecognized statement {statement!r}")

    if graph.outputs is None:
        raise DslError(line, "expected an output statement")
    if len(graph.inputs) > MAX_GRAPH_INPUTS:
        raise DslError(line, f"more than {MAX_GRAPH_INPUTS} inputs")
    if len(graph.outputs) > MAX_GRAPH_OUTPUTS:
        raise DslError(line, f"more than {MAX_GRAPH_OUTPUTS} outputs")
    if len(graph.ids) > MAX_NODES:
        raise DslError(line, f"more than {MAX_NODES} nodes")
    for call in graph.calls:
        missing = [n for n, _, _ in graph.inputs if n not in call.inputs]
        if missing:
            raise DslError(line, f"call {call.label} has no value for "
                           f"{', '.join(missing)}")
    return graph

#
# Graphcode
#


def _u16(n):
    """The interpreter reads graphcode with memcpy, so in host order, which is
    little-endian on x86"""
    return struct.pack("<H", n)


def _shape_bytes(dims):
    return bytes([len(dims)]) + b"".join(map(_u16, dims))


def _param_bytes(kind, param):
    if kind == "shape":
        return _shape_bytes(param)
    if kind == "dtype":
        return bytes([param.id])
    if kind in ("axis", "bits"):
        return bytes([param])
    if kind == "int64":
        return struct.pack("<q", param)
    if kind == "type":
        return bytes([param[0].id]) + _shape_bytes(param[1])
    if kind == "address":
        return param
    if kind == "offset":
        return struct.pack("<I", param)
    return (bytes([param.dtype.id]) + _shape_bytes(param.dims)
            + param.dtype.encode(param.values, "little"))


def data_code(*tensors):
    """The code of an account holding `tensors` for tensorref: a 0x00 byte, so
    that a call to the account stops at once, then each tensor encoded as a
    literal is, one after another"""
    return b"\0" + b"".join(_param_bytes("tensor", t) for t in tensors)


def graphcode(graph):
    code = _u16(MAGIC) + bytes([len(graph.inputs)])
    for _, dtype, dims in graph.inputs:
        code += bytes([dtype.id]) + _shape_bytes(dims)
    code += bytes([len(graph.outputs)]) + b"".join(map(_u16, graph.outputs))
    code += _u16(len(graph.nodes))
    for node in graph.nodes:
        op, kinds = OPS[node.op]
        code += _u16(OP_IDS[op])
        param_kinds = [k for k in kinds if k != "node"]
        code += b"".join(_param_bytes(kind, param)
                         for kind, param in zip(param_kinds, node.params))
        code += b"".join(map(_u16, node.inputs))
    return code

#
# JSON graphs
#


# Op names in JSON graphs, as in graph.hpp, and the DSL's for them
_JSON_OPS = {
    "Literal": "literal", "Add": "add", "Sub": "sub", "Mul": "mul",
    "Max": "max", "Min": "min", "Greater": "greater", "Ge": "ge",
    "Equal": "equal", "Where": "where", "Reshape": "reshape",
    "Saturate": "saturate", "Expand": "expand", "CumSum": "cumsum",
    "Div": "div", "MatMul": "matmul", "ArgMax": "argmax",
}


def _nest(values, dims):
    """Row-major `values` as lists nested to `dims`"""
    if not dims:
        return values[0]
    step = len(values) // dims[0] if dims[0] else 0
    return [_nest(values[i * step:(i + 1) * step], dims[1:])
            for i in range(dims[0])]


def json_to_dsl(text):
    """The statements for a graph in the JSON form of mnist.json"""
    graph = json.loads(text)
    lines = [f"input t{i}: {tensor['dtype']}{tensor['shape']}"
             for i, tensor in enumerate(graph["inputs"])]
    for id, node in enumerate(graph["nodes"], len(graph["inputs"])):
        op, params = node["op"], node.get("parameters", {})
        if op not in _JSON_OPS:
            raise ValueError(f"node {id}: unsupported op {op}")
        args = [f"t{i}" for i in node["inputs"]]
        try:
            if op == "Literal":
                args = [f"{params['dtype']}{params['shape']} "
                        f"{_nest(params['data'], params['shape'])}"]
            elif op in ("Reshape", "Expand"):
                args.append(str(params["shape"]))
            elif op == "Saturate":
                args.append(params["output_dtype"])
            elif op == "CumSum":
                args.append(str(params["axis"]))
            elif op == "Div":
                args.append(str(params["denominator"]))
        except KeyError as e:
            raise ValueError(f"node {id}: {op} has no parameter {e}") from None
        lines.append(f"t{id} = {_JSON_OPS[op]}({', '.join(args)})")
    lines.append("output " + ", ".join(f"t{i}" for i in graph["outputs"]))
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("graph", type=Path,
                        help="a graph, or a JSON graph with --from-json")
    parser.add_argument("-o", "--output", type=Path,
                        help="default: standard output")
    parser.add_argument("--from-json", action="store_true",
                        help="convert a JSON graph to this format instead")
    args = parser.parse_args()

    text = args.graph.read_text()
    try:
        result = (json_to_dsl(text) if args.from_json
                  else graphcode(parse(text)).hex() + "\n")
    except (DslError, ValueError, KeyError) as e:
        parser.exit(1, f"{args.graph}: {e}\n")
    if args.output:
        args.output.write_text(result)
    else:
        print(result, end="")


if __name__ == "__main__":
    main()
