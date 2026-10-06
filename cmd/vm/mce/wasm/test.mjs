// Copyright (C) 2026 Category Labs, Inc.
// SPDX-License-Identifier: GPL-3.0-or-later

import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';

const modulePath = process.argv[2] ?? 'build-mce-wasm/mce-wasm.mjs';
const nativePath = process.argv[3];
const {default: createMce} = await import(pathToFileURL(resolve(modulePath)));
const mce = await createMce();
let checked = 0;

// Spill traversal uses pointer-ordered containers. Allocation and the C++
// library can reorder adjacent, independent stores on native versus WASM.
function normalizeSpills(assembly) {
    const lines = assembly.split('\n');
    const spill = /^vmovaps qword ptr \[rbp(?:[+-]\d+)?\], ymm\d+$/;
    for (let i = 0; i < lines.length;) {
        if (!spill.test(lines[i])) { ++i; continue; }
        let end = i + 1;
        while (end < lines.length && spill.test(lines[end])) ++end;
        const stores = lines.slice(i, end);
        const offsets = stores.map(s => Number(s.match(/\[rbp([+-]\d+)?\]/)[1] ?? 0));
        assert.ok(offsets.every(n => n % 32 === 0));
        assert.equal(new Set(offsets).size, offsets.length, 'Overlapping stores');
        lines.splice(i, end - i, ...stores.sort());
        i = end;
    }
    return lines.join('\n');
}

function check(hex, revision = 'latest') {
    const result = mce.compileHex(hex, revision);
    assert.equal(result.error, '', `${revision}: ${hex}: ${result.error}`);
    assert.match(result.assembly, /ContractEpilogue:/);
    assert.match(result.assembly, /vzeroupper/);
    for (const call of result.assembly.matchAll(/^call qword ptr \[([^\]]+)\]/gm)) {
        assert.doesNotMatch(call[1], /^ROD(?:\+|$)/);
        assert.equal(result.assembly.split('\n').filter(line => line === `${call[1]}:`).length, 1,
            `Missing or duplicate function-pointer slot: ${call[1]}`);
    }
    if (nativePath) {
        const native = spawnSync(resolve(nativePath), [revision, hex], {
            encoding: 'utf8', timeout: 10000, maxBuffer: 16 * 1024 * 1024,
            stdio: ['ignore', 'pipe', 'pipe'],
        });
        assert.ifError(native.error);
        assert.equal(native.status, 0, native.stderr);
        assert.equal(normalizeSpills(result.assembly), normalizeSpills(native.stdout), `${revision}: ${hex}`);
    }
    ++checked;
    return result.assembly;
}

const fixtures = [
    '', '00',
    '600160020260005200', // Constant folding and memory expansion.
    '6000356001350460005200', // Dynamic division.
    '6000356001356002350860005200', // ADDMOD.
    '6000356001356002350960005200', // MULMOD.
    '6000356001350a60005200', // EXP.
    '60003160013b60023f00', // Host/environment calls.
    '600060003760006000f3', // Copy calldata and return memory.
    '600160005560005400', // Storage.
    '600060005d60005c00', // Transient storage (revision dependent).
    '600035565b60006000fd', // Dynamic jump table and revert.
    '600035600857005b00', // Conditional jump.
    '7f01', // Truncated PUSH32.
    '303233343536383a3d414243444546484a00', // Runtime/EVMC field offsets.
    '6000600060006000600060006000f100', // CALL ABI.
    '6000600060006000f500', // CREATE2 ABI.
];
const revisions = [
    'berlin', 'london', 'paris', 'shanghai', 'cancun', 'prague', 'osaka',
    'amsterdam', 'latest',
    ...['zero', 'one', 'two', 'three', 'four', 'five', 'six', 'seven',
        'eight', 'nine', 'ten', 'next'].map(r => `monad_${r}`),
];
for (const revision of revisions) {
    for (const fixture of fixtures) check(fixture, revision);
}
// Exercise every opcode with dynamic inputs, including invalid instructions.
for (let opcode = 0; opcode < 256; ++opcode) {
    check('600035'.repeat(7) + opcode.toString(16).padStart(2, '0') + '00'.repeat(33));
}
const baseline = check('60003560013504');
check('60003100');
assert.equal(check('60003560013504'), baseline, 'Compilation history changed assembly');
assert.match(check('60003100'), /runtime::balance/);
assert.match(check('600160005200'), /monad_vm_runtime_increase_memory_raw_v1/);
const symbolic = check('6000316000356001350460005200');
const pool = [];
const slots = new Map();
let inPool = false;
for (const line of symbolic.split('\n')) {
    if (line === 'ROD:') inPool = true;
    if (!inPool) continue;
    if (line.endsWith(':')) slots.set(line.slice(0, -1), pool.length);
    if (line.startsWith('.db ')) {
        pool.push(...line.match(/0x[0-9A-Fa-f]{2}/g).map(byte => Number.parseInt(byte, 16)));
    }
}
for (const [label, name] of [
    ['runtime_balance_ptr', 'runtime::balance<traits>'],
    ['runtime_udiv_ptr', 'runtime::udiv'],
    ['monad_vm_runtime_load_bounded_le_raw_ptr', 'monad_vm_runtime_load_bounded_le_raw'],
    ['monad_vm_runtime_increase_memory_raw_v1_ptr', 'monad_vm_runtime_increase_memory_raw_v1'],
]) {
    assert.ok(symbolic.includes(`call qword ptr [${label}]`), label);
    const offset = slots.get(label);
    assert.notEqual(offset, undefined, label);
    const address = pool.slice(offset, offset + 8).reduce((n, byte, index) => n | (BigInt(byte) << BigInt(index * 8)), 0n);
    assert.ok(symbolic.includes(`// Runtime placeholder 0x${address.toString(16).padStart(16, '0')}: ${name}`), label);
}
const repeated = check('60003160003100');
assert.equal(repeated.split('\n').filter(line => line === 'runtime_balance_ptr:').length, 1);
assert.equal(repeated.split('\n').filter(line => line === 'call qword ptr [runtime_balance_ptr]').length, 2);
assert.equal(check(' 0X60 01\n60 02 01 00 '), check('600160020100'));
for (const [source, revision, error] of [
    ['0', 'latest', /byte pairs/],
    ['0g', 'latest', /Malformed hex/],
    ['00\0', 'latest', /byte pairs/],
    ['00', 'unknown', /Unsupported revision/],
    ['00'.repeat(1 << 20), 'latest', /smaller than 1 MiB/],
    [' '.repeat(4 * 1024 * 1024 + 1), 'latest', /exceeds 4 MiB/],
]) {
    const result = mce.compileHex(source, revision);
    assert.equal(result.assembly, '');
    assert.match(result.error, error);
}
check('600160020100'); // Errors must leave the module reusable.
for (const [source, hex] of [
    ['push1 1 push2 0x0002 add stop', '60016100020100'],
    ['// comment\npush 0 push 255 push 256', '5f60ff610100'],
    ['push .end jump jumpdest .end stop', '6003565b00'],
    ['jumpdest .start push .start jump', '5b5f56'],
    ['push32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff stop', `7f${'ff'.repeat(32)}00`],
    ['', ''],
]) {
    const assembled = mce.assembleMnemonic(source);
    assert.equal(assembled.error, '', source);
    assert.equal(assembled.bytecode, hex, source);
    assert.equal(assembled.sourceLines.length, hex.length / 2);
    check(assembled.bytecode);
    if (nativePath) {
        const native = spawnSync(resolve(nativePath), ['latest', source, '--bytecode'], {encoding: 'utf8'});
        assert.equal(native.status, 0, native.stderr);
        assert.equal(native.stdout.trim(), hex);
    }
}
assert.deepEqual(mce.assembleMnemonic('// comment\npush2 0xabcd\nstop').sourceLines, [2, 2, 2, 3]);
for (const source of ['push1', 'push1 256', 'push .missing', 'jumpdest .x jumpdest .x',
    'wat', 'push -1', 'push 0xgg', '0xff', 'stop;', 'stop\0add']) {
    const result = mce.assembleMnemonic(source);
    assert.notEqual(result.error, '', source);
    assert.equal(result.bytecode, '');
    assert.deepEqual(result.sourceLines, []);
}
assert.equal(mce.assembleMnemonic('push 42 stop').bytecode, '602a00');
console.log(`Passed ${checked} assembly cases, all revisions and input-error checks` +
    (nativePath ? ' (native parity, allowing independent spill reordering).' : '.'));
