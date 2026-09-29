#!/usr/bin/env python3
"""Benchmark a generated corpus on a real ZisK ELF under ziskemu.

    ZKVM_BENCH=<zkvm-bench checkout> bench.py --elf ELF --emu ZISKEMU \
        --arm plain|l2 --corpus DIR [DIR ...] --out CSV [--jobs N] [--no-cost]

Every `manifest.csv` under each DIR is read -- or, for a zkvm-bench generation
(`<n>.witness` beside `<n>.blockhash`), the canonical block hashes -- and two
things happen per witness, the first gating the second:

  verify   the public output equals what the generator recorded: the block
           hash on the plaintext arm; parent hash | block hash | anchor |
           number (u64 BE) on the L2 arm. A guest that aborts leaves ziskemu at
           rc=0 with a zero output, so a run is judged on its bytes, never its
           exit status -- and a cost measured on an aborted run is the cost of
           an abort, so a row that fails verification carries no figures.
  measure  steps and COST exactly as zkvm-bench's compare.py takes them: its
           run_zisk, imported rather than copied, so a figure here and one in a
           compare report come from one parser.

Every manifest column is carried into the output row, so the regressors
(witness bytes, digests, leaves, gas) sit beside the cost they explain.
bench-report.py turns the CSVs into tables.
"""
import argparse
import csv
import os
import pathlib
import struct
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor

if 'ZKVM_BENCH' not in os.environ:
    sys.exit('set ZKVM_BENCH to a zkvm-bench checkout: its profiling/compare.py '
             'is the parser every figure goes through')
sys.path.insert(0, str(pathlib.Path(os.environ['ZKVM_BENCH']) / 'profiling'))
import compare  # noqa: E402

CATS = ('Base', 'Main', 'Opcodes', 'Precompiles', 'Memory')


def hx(s):
    return bytes.fromhex(s[2:] if s.startswith('0x') else s)


def expected(row, arm):
    if arm == 'plain':
        return hx(row['block_hash'])
    return (hx(row['parent_hash']) + hx(row['block_hash'])
            + hx(row['anchor']) + struct.pack('>Q', int(row['number'])))


def verify(emu, elf, wit, want):
    with tempfile.TemporaryDirectory() as t:
        inp, out = pathlib.Path(t) / 'in.bin', pathlib.Path(t) / 'out.bin'
        compare.frame_ziskos(str(wit), str(inp))
        r = subprocess.run([emu, '-e', elf, '-i', str(inp), '-o', str(out)],
                           capture_output=True, text=True)
        got = out.read_bytes() if out.exists() else b''
    if got[:len(want)] == want:
        return 'PASS'
    if got[:len(want)] == bytes(len(want)):
        return 'ABORT'
    return f'MISMATCH(rc={r.returncode})'


def one(job):
    emu, elf, arm, wit, row, with_cost = job
    out = dict(row)
    out['corpus'] = wit.parent.name
    out['verdict'] = verify(emu, elf, wit, expected(row, arm))
    if out['verdict'] != 'PASS':
        return out
    r = compare.run_zisk(emu, elf, str(wit), 'monad', with_cost=with_cost)
    if 'error' in r:
        out['verdict'] = 'EMU-ERROR'
        return out
    out['steps'] = r['work']
    out['emu_secs'] = r['secs']
    if with_cost:
        out['cost'] = r.get('cost')
        for c in CATS:
            out[c.lower()] = (r.get('cats') or {}).get(c)
        ops = r.get('ops') or {}
        out['kec_calls'] = r.get('kec')
        out['kec_cost'] = r.get('kec_cost')
        out['poseidon2_cost'] = ops.get('poseidon2')
        out['secp256k1_cost'] = sum(v for k, v in ops.items()
                                    if k.startswith('secp256k1'))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--elf', required=True)
    ap.add_argument('--emu', required=True)
    ap.add_argument('--arm', choices=('plain', 'l2'), required=True)
    ap.add_argument('--corpus', nargs='+', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--no-cost', action='store_true')
    a = ap.parse_args()

    jobs = []
    for d in map(pathlib.Path, a.corpus):
        manifests = sorted(d.rglob('manifest.csv'))
        for m in manifests:
            for row in csv.DictReader(open(m)):
                w = m.parent / f"{row['scenario']}-{int(row['number']):08d}.witness"
                jobs.append((a.emu, a.elf, a.arm, w, row, not a.no_cost))
        if manifests:
            continue
        # A zkvm-bench generation instead: <n>.witness beside <n>.blockhash,
        # the canonical hash the plaintext arm must reproduce.
        for w in sorted(d.glob('*.witness')):
            ref = w.with_suffix('.blockhash')
            if a.arm != 'plain' or not ref.exists():
                sys.exit(f'{w}: no manifest.csv, and no .blockhash for the plaintext arm')
            h = ref.read_text().strip()
            row = {'scenario': 'mainnet', 'number': w.stem,
                   'block_hash': h if h.startswith('0x') else '0x' + h,
                   'witness_bytes': w.stat().st_size}
            jobs.append((a.emu, a.elf, a.arm, w, row, not a.no_cost))
    if not jobs:
        sys.exit('no manifest rows under ' + ' '.join(a.corpus))

    rows = []
    with ProcessPoolExecutor(a.jobs) as ex:
        for i, r in enumerate(ex.map(one, jobs), 1):
            rows.append(r)
            if i % 25 == 0 or i == len(jobs):
                print(f'  {i}/{len(jobs)}', file=sys.stderr, flush=True)

    keys = []
    for r in rows:
        keys += [k for k in r if k not in keys]
    with open(a.out, 'w', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=keys)
        w.writeheader()
        w.writerows(rows)
    bad = [r for r in rows if r['verdict'] != 'PASS']
    print(f'{len(rows) - len(bad)} PASS, {len(bad)} not ({a.arm}) -> {a.out}')
    for r in bad[:10]:
        print(f"   {r['corpus']}/{r['scenario']}-{r['number']}: {r['verdict']}")
    return 1 if bad else 0


if __name__ == '__main__':
    sys.exit(main())
