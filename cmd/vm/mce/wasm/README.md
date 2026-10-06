# MCE assembly-only WebAssembly target

Builds the existing Monad x86-64 compiler as a browser module. It accepts hex
EVM bytecode or assembles `.mevm` mnemonics, and returns AsmJit's Intel-syntax
assembly listing, including EVM instruction comments. It does not execute contracts or install generated code.

## Build

From the repository root, with the repository submodules initialized and
[Emscripten](https://emscripten.org/docs/getting_started/downloads.html) activated:

```sh
emcmake cmake -S cmd/vm/mce/wasm -B build-mce-wasm -G Ninja \
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-mce-wasm --target mce-wasm -j8
ctest --test-dir build-mce-wasm --output-on-failure
```

Tested with Emscripten **6.0.11**. The standalone CMake project needs only the
vendored AsmJit, EVMC, ethash headers, and unordered_dense dependencies; it does
not build the node, execution runtime, or native MCE CLI.

The output is `build-mce-wasm/mce-wasm.mjs` and `mce-wasm.wasm`. Copy both files
together to a static host, including GitHub Pages. No server-side compiler,
threads, or cross-origin isolation headers are needed.

## API

```js
import createMce from './mce-wasm.mjs';

const mce = await createMce();
const {assembly, error} = mce.compileHex('600160020160005200', 'latest');
if (error) throw new Error(error);
console.log(assembly);
```

`compileHex(source, revision)` is synchronous. Both arguments are strings.
Run it in a Web Worker when connecting it to an editor, so compilation does
not block the UI. A worker can be terminated and recreated to cancel a compile.

The source may contain whitespace and an optional `0x` prefix. Empty bytecode
is valid. Invalid hex, unknown revisions, and size-limit errors return an
empty `assembly` and a nonempty `error`; successful calls return an empty
`error`. Source is limited to 4 MiB and decoded bytecode to less than 1 MiB.
Solidity source is not supported.

`assembleMnemonic(source)` assembles native MCE `.mevm` syntax and returns
`{bytecode, sourceLines, error}`. `bytecode` is lowercase hex without a prefix;
`sourceLines` is a JavaScript array containing the one-based source line of each
emitted byte. Errors return empty output and leave the module reusable.

```js
const parsed = mce.assembleMnemonic('push1 1\npush 42\nadd\nstop');
if (parsed.error) throw new Error(parsed.error);
console.log(parsed.bytecode); // 6001602a0100
console.log(mce.compileHex(parsed.bytecode, 'latest').assembly);
```

Opcodes are case-insensitive. Constants may be decimal or `0x` hex; `PUSH`
chooses the smallest width, while `PUSH1` through `PUSH32` fix the width.
`//` comments and labels (`push .end jump jumpdest .end`) are supported.
The assembler uses the same latest-stable instruction set as native MCE;
the selected revision controls the subsequent x86 compilation. Strict parsing
rejects unknown tokens, overflowing immediates, duplicate labels, and undefined
labels, without imposing stack validation on snippets.

Revision names are case-insensitive: `berlin`, `london`, `paris`, `shanghai`,
`cancun`, `prague`, `osaka`, `amsterdam`, `latest`, and `monad_zero` through
`monad_ten`, plus `monad_next`. `latest` follows
`MONAD_ETH_LATEST_STABLE_REVISION`, as in the native MCE CLI.

For a future static Compiler Explorer adapter, the result can be converted to
CE's basic compilation response shape:

```js
const result = mce.compileHex(source, revision);
const response = {
    code: result.error ? 1 : 0,
    asm: result.assembly.split('\n').filter(Boolean).map(text => ({text})),
    stdout: [],
    stderr: result.error ? [{text: result.error}] : [],
};
```

This target does not yet bundle CE or implement its frontend transport.

## Cross-compilation details

The shared emitter now separates assembly emission from JIT installation.
The WASM build disables AsmJit's JIT allocator and explicitly targets Linux
x86-64. It reuses the portable arithmetic primitives already used by the zkVM
build for compile-time constant folding.

`-sMEMORY64=2` preserves 64-bit C++ pointers and the native runtime data layout,
then lowers the module to wasm32. This matters because the emitter embeds
`Context`, `Memory`, and EVMC structure offsets in the x86 output. The browser
needs WebAssembly and JavaScript BigInt, but not native memory64 support.

Runtime helpers are represented by deterministic placeholder addresses. The
listing gives each function-pointer slot a symbolic label, for example
`call qword ptr [runtime_balance_ptr]`. These names remain visible when comments
are hidden. The pointer bytes are placeholders, not executable native addresses. This mode is compile-only and is rejected at build time if
AsmJit's JIT support is enabled.

## Native parity check

An optional native build of the same standalone target checks layout and
constant-folding parity without running generated code:

```sh
cmake -S cmd/vm/mce/wasm -B build-mce-native -G Ninja \
    -DCMAKE_BUILD_TYPE=Release
cmake --build build-mce-native -j8
node cmd/vm/mce/wasm/test.mjs \
    build-mce-wasm/mce-wasm.mjs build-mce-native/mce-wasm
```

The checks cover every opcode, all supported revisions, malformed inputs,
repeated compilation, runtime calls, memory/context offsets, jumps, and
constant folding. Native/WASM comparisons allow reordering of adjacent,
non-overlapping stack spill stores, since pointer-ordered containers can
visit them in different orders.
